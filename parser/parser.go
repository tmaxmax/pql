// Copyright 2024 RunReveal Inc.
// SPDX-License-Identifier: Apache-2.0

// Package parser provides a parser and an Abstract Syntax Tree (AST) for the Pipeline Query Language.
package parser

import (
	"errors"
	"fmt"
	"slices"
	"strings"

	"golang.org/x/exp/maps"
)

type parser struct {
	source string
	tokens []Token
	pos    int

	splitKind TokenKind
}

// Parse converts a Pipeline Query Language query
// into an Abstract Syntax Tree (AST).
func Parse(query string) ([]Statement, error) {
	p := &parser{
		source: query,
		tokens: Scan(query),
	}
	var result []Statement
	var resultError error
	for {
		stmtParser := p.splitSemi()

		stmt, err := firstParse(
			func() (Statement, error) {
				stmt, err := stmtParser.letStatement()
				if stmt == nil {
					// Prevent returning a non-nil interface.
					return nil, err
				}
				return stmt, err
			},
			func() (Statement, error) {
				expr, err := stmtParser.tabularExpr()
				if expr == nil {
					// Prevent returning a non-nil interface.
					return nil, err
				}
				return expr, err
			},
			func() (Statement, error) {
				macro, err := stmtParser.macro()
				if macro == nil {
					// Prevent returning a non-nil interface.
					return nil, err
				}
				return macro, err
			},
		)

		if isNotFound(err) {
			// We're okay with empty statements, we just ignore them.
			if stmtParser.pos < len(stmtParser.tokens) {
				trailingToken := stmtParser.tokens[stmtParser.pos]
				if trailingToken.Kind == TokenError {
					resultError = joinErrors(err, &parseError{
						source: p.source,
						span:   trailingToken.Span,
						err:    errors.New(trailingToken.Value),
					})
				} else {
					resultError = joinErrors(err, &parseError{
						source: p.source,
						span:   trailingToken.Span,
						err:    errors.New("unrecognized token"),
					})
				}
			}
		} else {
			if stmt != nil {
				result = append(result, stmt)
			}
			resultError = joinErrors(resultError, makeErrorOpaque(err))
			resultError = joinErrors(resultError, stmtParser.endSplit())
		}

		// Next token, if present, guaranteed to be a semicolon.
		if _, ok := p.next(); !ok {
			break
		}
	}

	if resultError != nil {
		return result, fmt.Errorf("parse pipeline query language: %w", resultError)
	}
	return result, nil
}

func firstParse[T any](productions ...func() (T, error)) (T, error) {
	for _, p := range productions[:len(productions)-1] {
		x, err := p()
		if !isNotFound(err) {
			return x, err
		}
	}
	return productions[len(productions)-1]()
}

func (p *parser) letStatement() (*LetStatement, error) {
	keyword, _ := p.next()
	if keyword.Kind != TokenIdentifier || keyword.Value != "let" {
		p.prev()
		return nil, &parseError{
			source: p.source,
			span:   keyword.Span,
			err:    notFoundError{fmt.Errorf("expected 'let', got %s", formatToken(p.source, keyword))},
		}
	}

	stmt := &LetStatement{
		Keyword: keyword.Span,
		Assign:  nullSpan(),
	}
	var err error
	stmt.Name, err = p.ident()
	if err != nil {
		return stmt, makeErrorOpaque(err)
	}
	assign, _ := p.next()
	if assign.Kind != TokenAssign {
		return stmt, &parseError{
			source: p.source,
			span:   assign.Span,
			err:    fmt.Errorf("expected '=', got %s", formatToken(p.source, assign)),
		}
	}
	stmt.Assign = assign.Span
	stmt.X, err = p.expr()
	if err != nil {
		return stmt, makeErrorOpaque(err)
	}

	if m, ok := stmt.X.(*Macro); ok && m.Macro.Name == "define" {
		d := &Define{
			Hash:    m.Hash,
			Keyword: m.Macro.Span(),
			Lparen:  m.Lparen,
			Rparen:  m.Rparen,
			Args:    make([]*Ident, 0, len(m.Args)),
		}
		stmt.X = d

		for _, arg := range m.Args {
			q, ok := arg.(*QualifiedIdent)
			if !ok || len(q.Parts) > 1 ||
				slices.Contains(reserved, q.Parts[0].Name) ||
				slices.ContainsFunc(d.Args, func(i *Ident) bool { return i.Name == q.Parts[0].Name }) {
				return stmt, &parseError{
					source: p.source,
					span:   m.Span(),
					err:    errors.New("define has illegal or duplicate identifiers"),
				}
			}

			d.Args = append(d.Args, q.Parts[0])
		}

		tokens := p.tokens[p.pos:]
		if len(tokens) == 0 {
			return stmt, &parseError{
				source: p.source,
				span:   m.Span(),
				err:    errors.New("empty define body"),
			}
		}

		spans := make([]Span, len(p.tokens[p.pos:]))
		for i, t := range tokens {
			spans[i] = t.Span
		}

		d.Body = func() (Node, error) {
			return parseNode(&parser{
				source:    p.source,
				tokens:    tokens,
				splitKind: p.splitKind,
			}, false)
		}
		d.BodySpan = unionSpans(spans...)

		p.pos = len(p.tokens) + 1
	}

	return stmt, nil
}

func (p *parser) tabularExpr() (*TabularExpr, error) {
	tableName, err := p.ident()
	if err != nil {
		return nil, err
	}
	expr := &TabularExpr{
		Source: &TableRef{Table: tableName},
	}

	var finalError error
	for i := 0; ; i++ {
		pipeToken, _ := p.next()
		if pipeToken.Kind != TokenPipe {
			p.prev()
			return expr, finalError
		}

		opParser := p.split(TokenPipe)

		operatorName, ok := opParser.next()
		if !ok {
			expr.Operators = append(expr.Operators, &UnknownTabularOperator{
				Pipe: pipeToken.Span,
			})
			finalError = joinErrors(finalError, &parseError{
				source: opParser.source,
				span:   pipeToken.Span,
				err:    errors.New("missing operator name after pipe"),
			})
			continue
		}
		if operatorName.Kind == TokenHash {
			opParser.prev()
			m, err := opParser.macro()
			m.Pipe = pipeToken.Span
			expr.Operators = append(expr.Operators, m)
			finalError = joinErrors(finalError, err)
			continue
		}
		if operatorName.Kind != TokenIdentifier {
			expr.Operators = append(expr.Operators, &UnknownTabularOperator{
				Pipe:   pipeToken.Span,
				Tokens: opParser.tokens,
			})
			finalError = joinErrors(finalError, &parseError{
				source: opParser.source,
				span:   operatorName.Span,
				err:    fmt.Errorf("expected operator name, got %s", formatToken(opParser.source, operatorName)),
			})
			continue
		}
		switch operatorName.Value {
		case "count":
			op, err := opParser.countOperator(pipeToken, operatorName)
			if op != nil {
				expr.Operators = append(expr.Operators, op)
			}
			finalError = joinErrors(finalError, err)
		case "where", "filter":
			op, err := opParser.whereOperator(pipeToken, operatorName)
			if op != nil {
				expr.Operators = append(expr.Operators, op)
			}
			finalError = joinErrors(finalError, err)
		case "sort", "order":
			op, err := opParser.sortOperator(pipeToken, operatorName)
			if op != nil {
				expr.Operators = append(expr.Operators, op)
			}
			finalError = joinErrors(finalError, err)
		case "take", "limit":
			op, err := opParser.takeOperator(pipeToken, operatorName)
			if op != nil {
				expr.Operators = append(expr.Operators, op)
			}
			finalError = joinErrors(finalError, err)
		case "top":
			op, err := opParser.topOperator(pipeToken, operatorName)
			if op != nil {
				expr.Operators = append(expr.Operators, op)
			}
			finalError = joinErrors(finalError, err)
		case "project":
			op, err := opParser.projectOperator(pipeToken, operatorName)
			if op != nil {
				expr.Operators = append(expr.Operators, op)
			}
			finalError = joinErrors(finalError, err)
		case "extend":
			op, err := opParser.extendOperator(pipeToken, operatorName)
			if op != nil {
				expr.Operators = append(expr.Operators, op)
			}
			finalError = joinErrors(finalError, err)
		case "summarize":
			op, err := opParser.summarizeOperator(pipeToken, operatorName)
			if op != nil {
				expr.Operators = append(expr.Operators, op)
			}
			finalError = joinErrors(finalError, err)
		case "join":
			op, err := opParser.joinOperator(pipeToken, operatorName)
			if op != nil {
				expr.Operators = append(expr.Operators, op)
			}
			finalError = joinErrors(finalError, err)
		case "as":
			op, err := opParser.asOperator(pipeToken, operatorName)
			if op != nil {
				expr.Operators = append(expr.Operators, op)
			}
			finalError = joinErrors(finalError, err)
		case "render":
			op, err := opParser.renderOperator(pipeToken, operatorName)
			if op != nil {
				expr.Operators = append(expr.Operators, op)
			}
			finalError = joinErrors(finalError, err)

		default:
			expr.Operators = append(expr.Operators, &UnknownTabularOperator{
				Pipe:   pipeToken.Span,
				Tokens: opParser.tokens,
			})
			finalError = joinErrors(finalError, &parseError{
				source: opParser.source,
				span:   operatorName.Span,
				err:    fmt.Errorf("unknown operator name %q", operatorName.Value),
			})
			continue
		}

		finalError = joinErrors(finalError, opParser.endSplit())
	}
}

func (p *parser) countOperator(pipe, keyword Token) (*CountOperator, error) {
	return &CountOperator{
		Pipe:    pipe.Span,
		Keyword: keyword.Span,
	}, nil
}

func (p *parser) whereOperator(pipe, keyword Token) (*WhereOperator, error) {
	x, err := p.expr()
	err = makeErrorOpaque(err)
	return &WhereOperator{
		Pipe:      pipe.Span,
		Keyword:   keyword.Span,
		Predicate: x,
	}, err
}

func (p *parser) sortOperator(pipe, keyword Token) (*SortOperator, error) {
	by, _ := p.next()
	if by.Kind != TokenBy {
		op := &SortOperator{
			Pipe:    pipe.Span,
			Keyword: keyword.Span,
		}
		err := &parseError{
			source: p.source,
			span:   by.Span,
			err:    fmt.Errorf("expected 'by', got %s", formatToken(p.source, by)),
		}
		return op, err
	}

	op := &SortOperator{
		Pipe:    pipe.Span,
		Keyword: newSpan(keyword.Span.Start, by.Span.End),
	}
	for {
		term, err := p.sortTerm()
		if term != nil {
			op.Terms = append(op.Terms, term)
		}
		if err != nil {
			return op, makeErrorOpaque(err)
		}

		// Check for a comma to see if we should proceed.
		if tok, _ := p.next(); tok.Kind != TokenComma {
			p.prev()
			return op, nil
		}
	}
}

func (p *parser) sortTerm() (*SortTerm, error) {
	x, err := p.expr()
	if err != nil {
		return nil, err
	}
	term := &SortTerm{
		X:           x,
		AscDescSpan: nullSpan(),
		NullsSpan:   nullSpan(),
	}

	// asc/desc
	tok, ok := p.next()
	if !ok {
		if m, ok := x.(*Macro); ok {
			term.Macro = m
			term.X = nil
		}
		return term, nil
	}

	switch tok.Kind {
	case TokenIdentifier:
		switch tok.Value {
		case "asc":
			term.Asc = true
			term.AscDescSpan = tok.Span
			term.NullsFirst = true
		case "desc":
			term.Asc = false
			term.AscDescSpan = tok.Span
			term.NullsFirst = false
		case "nulls":
			// Good, but wait until next switch statement.
			p.prev()
		default:
			p.prev()
			return term, nil
		}
	case TokenHash:
		p.prev()
		m, err := p.macro()
		if err != nil {
			return nil, err
		}
		term.Macro = m
	default:
		if m, ok := x.(*Macro); ok {
			term.Macro = m
			term.X = nil
		}
		p.prev()
		return term, nil
	}

	// nulls first/last
	tok, ok = p.next()
	if !ok {
		return term, nil
	}
	switch {
	case tok.Kind == TokenIdentifier && tok.Value == "nulls":
		switch tok2, _ := p.next(); {
		case tok2.Kind == TokenIdentifier && tok2.Value == "first":
			term.NullsFirst = true
			term.NullsSpan = newSpan(tok.Span.Start, tok2.Span.End)
		case tok2.Kind == TokenIdentifier && tok2.Value == "last":
			term.NullsFirst = false
			term.NullsSpan = newSpan(tok.Span.Start, tok2.Span.End)
		default:
			p.prev()
			return term, &parseError{
				source: p.source,
				span:   tok2.Span,
				err:    fmt.Errorf("expected 'first' or 'last', got %s", formatToken(p.source, tok2)),
			}
		}
	default:
		p.prev()
		return term, nil
	}

	return term, nil
}

func (p *parser) takeOperator(pipe, keyword Token) (*TakeOperator, error) {
	op := &TakeOperator{
		Pipe:    pipe.Span,
		Keyword: keyword.Span,
	}
	var err error
	op.RowCount, err = p.rowCount()
	if err != nil {
		return op, makeErrorOpaque(err)
	}
	return op, nil
}

func (p *parser) topOperator(pipe, keyword Token) (*TopOperator, error) {
	op := &TopOperator{
		Pipe:    pipe.Span,
		Keyword: keyword.Span,
		By:      nullSpan(),
	}

	var err error
	op.RowCount, err = p.rowCount()
	if err != nil {
		return op, makeErrorOpaque(err)
	}

	tok, _ := p.next()
	if tok.Kind != TokenBy {
		p.prev()
		return op, &parseError{
			source: p.source,
			span:   tok.Span,
			err:    fmt.Errorf("expected 'by', got %s", formatToken(p.source, tok)),
		}
	}
	op.By = tok.Span

	op.Col, err = p.sortTerm()
	return op, makeErrorOpaque(err)
}

func (p *parser) rowCount() (Expr, error) {
	x, err := p.expr()
	if err != nil {
		return x, err
	}
	if lit, ok := x.(*BasicLit); ok {
		// Do basic check for common case of literals.
		if !lit.IsInteger() {
			return x, fmt.Errorf("expected integer, got %s", formatToken(p.source, Token{
				Kind:  lit.Kind,
				Span:  lit.ValueSpan,
				Value: lit.Value,
			}))
		}
	}
	return x, nil
}

func (p *parser) projectOperator(pipe, keyword Token) (*ProjectOperator, error) {
	op := &ProjectOperator{
		Pipe:    pipe.Span,
		Keyword: keyword.Span,
	}

	for {
		m, err := p.macro()
		if isNotFound(err) {
			err = nil
		} else if err != nil {
			return op, makeErrorOpaque(err)
		}

		colName, err := p.ident()
		if err != nil {
			if m == nil || !isNotFound(err) {
				return op, makeErrorOpaque(err)
			}
		}
		col := &ProjectColumn{
			Macro:  m,
			Name:   colName,
			Assign: nullSpan(),
		}
		op.Cols = append(op.Cols, col)

		sep, ok := p.next()
		if !ok {
			return op, nil
		}
		switch sep.Kind {
		case TokenComma:
			continue
		case TokenAssign:
			col.Assign = sep.Span
			col.X, err = p.expr()
			if err != nil {
				return op, makeErrorOpaque(err)
			}
			sep, ok = p.next()
			if !ok {
				return op, nil
			}
			if sep.Kind != TokenComma {
				return op, fmt.Errorf("expected ',' or EOF, got %s", formatToken(p.source, sep))
			}
		default:
			p.prev()
			return op, nil
		}
	}
}

func (p *parser) extendOperator(pipe, keyword Token) (*ExtendOperator, error) {
	op := &ExtendOperator{
		Pipe:    pipe.Span,
		Keyword: keyword.Span,
	}

	for {
		col, err := p.extendColumn()
		if err != nil {
			return op, makeErrorOpaque(err)
		}
		op.Cols = append(op.Cols, col)

		sep, ok := p.next()
		if !ok {
			return op, nil
		}
		if sep.Kind != TokenComma {
			p.prev()
			return op, nil
		}
	}
}

func (p *parser) renderOperator(pipe, keyword Token) (*RenderOperator, error) {
	op := &RenderOperator{
		Pipe:    pipe.Span,
		Keyword: keyword.Span,
		With:    nullSpan(),
		Lparen:  nullSpan(),
		Rparen:  nullSpan(),
	}

	// Parse chart type (required)
	chartType, err := p.ident()
	if err != nil {
		return op, &parseError{
			source: p.source,
			span:   keyword.Span,
			err:    fmt.Errorf("expected chart type after render, got %v", err),
		}
	}
	op.ChartType = chartType

	// Look for optional "with" clause
	tok, ok := p.next()
	if !ok {
		return op, nil
	}

	if tok.Kind != TokenIdentifier || tok.Value != "with" {
		p.prev()
		return op, nil
	}
	op.With = tok.Span

	// Parse opening parenthesis
	tok, _ = p.next()
	if tok.Kind != TokenLParen {
		return op, &parseError{
			source: p.source,
			span:   tok.Span,
			err:    fmt.Errorf("expected '(' after with, got %s", formatToken(p.source, tok)),
		}
	}
	op.Lparen = tok.Span

	// Parse properties
	for {
		prop, err := p.renderProperty()
		if err != nil {
			return op, makeErrorOpaque(err)
		}
		if prop != nil {
			op.Props = append(op.Props, prop)
		}

		// Check for comma or closing parenthesis
		tok, _ = p.next()
		if tok.Kind == TokenRParen {
			op.Rparen = tok.Span
			break
		}
		if tok.Kind != TokenComma {
			return op, &parseError{
				source: p.source,
				span:   tok.Span,
				err:    fmt.Errorf("expected ',' or ')', got %s", formatToken(p.source, tok)),
			}
		}
	}

	return op, nil
}

func (p *parser) renderProperty() (*RenderProperty, error) {
	prop := &RenderProperty{
		Assign: nullSpan(),
	}

	// Parse property name
	name, err := p.ident()
	if err != nil {
		return nil, err
	}
	prop.Name = name

	// Parse equals sign
	tok, _ := p.next()
	if tok.Kind != TokenAssign {
		return nil, &parseError{
			source: p.source,
			span:   tok.Span,
			err:    fmt.Errorf("expected '=' after property name, got %s", formatToken(p.source, tok)),
		}
	}
	prop.Assign = tok.Span

	// Parse property value
	value, err := p.expr()
	if err != nil {
		return nil, err
	}
	prop.Value = value

	return prop, nil
}

func (p *parser) extendColumn() (*ExtendColumn, error) {
	restorePos := p.pos

	col := &ExtendColumn{
		Assign: nullSpan(),
	}

	var err error
	col.Name, err = p.ident()
	if err == nil {
		if assign, _ := p.next(); assign.Kind == TokenAssign {
			col.Assign = assign.Span
		} else {
			col.Name = nil
			p.pos = restorePos
		}
	} else if !isNotFound(err) {
		col.X = col.Name.AsQualified()
		col.Name = nil
		return col, makeErrorOpaque(err)
	}

	col.X, err = p.expr()
	if col.Name != nil {
		err = makeErrorOpaque(err)
	}

	if m, ok := col.X.(*Macro); ok && col.Name == nil {
		col.Macro = m
		col.X = nil
	}

	return col, err
}

func (p *parser) summarizeOperator(pipe, keyword Token) (*SummarizeOperator, error) {
	op := &SummarizeOperator{
		Pipe:    pipe.Span,
		Keyword: keyword.Span,
		By:      nullSpan(),
	}

	for {
		col, err := p.summarizeColumn()
		if isNotFound(err) {
			break
		}
		if col != nil {
			op.Cols = append(op.Cols, col)
		}
		if err != nil {
			return op, makeErrorOpaque(err)
		}

		sep, ok := p.next()
		if !ok {
			return op, nil
		}
		if sep.Kind != TokenComma {
			p.prev()
			break
		}
	}

	sep, ok := p.next()
	if !ok {
		if len(op.Cols) == 0 {
			return op, &parseError{
				source: p.source,
				span:   sep.Span,
				err:    fmt.Errorf("expected expression or 'by', got EOF"),
			}
		}
		return op, nil
	}
	if sep.Kind != TokenBy {
		p.prev()
		if len(op.Cols) == 0 {
			return op, &parseError{
				source: p.source,
				span:   sep.Span,
				err:    fmt.Errorf("expected expression or 'by', got %s", formatToken(p.source, sep)),
			}
		}
		return op, nil
	}
	op.By = sep.Span
	for {
		col, err := p.summarizeColumn()
		if isNotFound(err) {
			return op, makeErrorOpaque(err)
		}
		if col != nil {
			op.GroupBy = append(op.GroupBy, col)
		}
		if err != nil {
			return op, makeErrorOpaque(err)
		}

		sep, ok := p.next()
		if !ok {
			return op, nil
		}
		if sep.Kind != TokenComma {
			p.prev()
			return op, nil
		}
	}
}

func (p *parser) summarizeColumn() (*SummarizeColumn, error) {
	restorePos := p.pos

	col := &SummarizeColumn{
		Assign: nullSpan(),
	}

	var err error
	col.Name, err = p.ident()
	if err == nil {
		if assign, _ := p.next(); assign.Kind == TokenAssign {
			col.Assign = assign.Span
		} else {
			col.Name = nil
			p.pos = restorePos
		}
	} else if !isNotFound(err) {
		col.X = col.Name.AsQualified()
		col.Name = nil
		return col, makeErrorOpaque(err)
	}

	col.X, err = p.expr()
	if col.Name != nil {
		err = makeErrorOpaque(err)
	}
	return col, err
}

var joinTypes = map[string]struct{}{
	"innerunique": {},
	"inner":       {},
	"leftouter":   {},
}

func (p *parser) joinOperator(pipe, keyword Token) (*JoinOperator, error) {
	op := &JoinOperator{
		Pipe:       pipe.Span,
		Keyword:    keyword.Span,
		Kind:       nullSpan(),
		KindAssign: nullSpan(),
		Lparen:     nullSpan(),
		Rparen:     nullSpan(),
		On:         nullSpan(),
	}

	tok, ok := p.next()
	if !ok {
		return op, &parseError{
			source: p.source,
			span:   indexSpan(len(p.source)),
			err:    fmt.Errorf("expected 'kind' or '(', got EOF"),
		}
	}

	// Optional "kind = JoinFlavor" clause.
	var finalError error
	if tok.Kind == TokenIdentifier && tok.Value == "kind" {
		op.Kind = tok.Span
		tok, _ = p.next()
		if tok.Kind != TokenAssign {
			return op, joinErrors(finalError, &parseError{
				source: p.source,
				span:   tok.Span,
				err:    fmt.Errorf("expected '=', got %s", formatToken(p.source, tok)),
			})
		}
		op.KindAssign = tok.Span
		tok, _ = p.next()
		if tok.Kind != TokenIdentifier {
			return op, joinErrors(finalError, &parseError{
				source: p.source,
				span:   tok.Span,
				err:    fmt.Errorf("expected join flavor, got %s", formatToken(p.source, tok)),
			})
		}
		op.Flavor = &Ident{
			Name:     tok.Value,
			NameSpan: tok.Span,
		}
		if _, ok := joinTypes[tok.Value]; !ok {
			joinTypeList := maps.Keys(joinTypes)
			slices.Sort(joinTypeList)
			finalError = joinErrors(finalError, &parseError{
				source: p.source,
				span:   tok.Span,
				err:    fmt.Errorf("expected join flavor (one of %s), got %s", strings.Join(joinTypeList, ", "), tok.Value),
			})
		}
	} else {
		p.prev()
	}

	var err error

	// Right table:
	tok, _ = p.next()
	switch tok.Kind {
	case TokenLParen:
		op.Lparen = tok.Span
		rightParser := p.split(TokenRParen)
		op.Right, err = rightParser.tabularExpr()
		finalError = joinErrors(finalError, makeErrorOpaque(err), rightParser.endSplit())
		tok, _ = p.next()
		if tok.Kind != TokenRParen {
			return op, joinErrors(finalError, &parseError{
				source: p.source,
				span:   tok.Span,
				err:    fmt.Errorf("expected ')', got %s", formatToken(p.source, tok)),
			})
		}
		op.Rparen = tok.Span
	case TokenHash:
		p.prev()
		op.Macro, err = p.macro()
		if err != nil {
			return op, joinErrors(finalError, err)
		}
	default:
		return op, joinErrors(finalError, &parseError{
			source: p.source,
			span:   tok.Span,
			err:    fmt.Errorf("expected '(', got %s", formatToken(p.source, tok)),
		})
	}

	// Conditions:
	tok, _ = p.next()
	if tok.Kind != TokenIdentifier || tok.Value != "on" {
		return op, joinErrors(finalError, &parseError{
			source: p.source,
			span:   tok.Span,
			err:    fmt.Errorf("expected 'on', got %s", formatToken(p.source, tok)),
		})
	}
	op.On = tok.Span
	op.Conditions, err = p.exprList()
	finalError = joinErrors(finalError, makeErrorOpaque(err))

	return op, finalError
}

func (p *parser) asOperator(pipe, keyword Token) (*AsOperator, error) {
	op := &AsOperator{
		Pipe:    pipe.Span,
		Keyword: keyword.Span,
	}
	var err error
	op.Name, err = p.ident()
	return op, makeErrorOpaque(err)
}

// exprList parses one or more comma-separated expressions.
func (p *parser) exprList() ([]Expr, error) {
	first, err := p.expr()
	if err != nil {
		return nil, err
	}
	result := []Expr{first}
	for {
		restorePos := p.pos
		tok, ok := p.next()
		if !ok {
			return result, nil
		}
		if tok.Kind != TokenComma {
			p.prev()
			return result, nil
		}
		x, err := p.expr()
		if isNotFound(err) {
			p.pos = restorePos
			return result, nil
		}
		if x != nil {
			result = append(result, x)
		}
		if err != nil {
			// If there's a notFoundError, we want to mask it from the caller.
			return result, makeErrorOpaque(err)
		}
	}
}

func (p *parser) expr() (Expr, error) {
	x, err1 := p.unaryExpr()
	if isNotFound(err1) {
		return x, err1
	}
	x, err2 := p.exprBinaryTrail(x, 0)
	return x, joinErrors(err1, err2)
}

// exprBinaryTrail parses zero or more (binaryOp, unaryExpr) sequences.
func (p *parser) exprBinaryTrail(x Expr, minPrecedence int) (Expr, error) {
	var finalError error
	for {
		op1, ok := p.next()
		if !ok {
			return x, finalError
		}
		precedence1 := operatorPrecedence(op1.Kind)
		if precedence1 < 0 || precedence1 < minPrecedence {
			// Not a binary operator or below precedence threshold.
			p.prev()
			return x, finalError
		}

		if op1.Kind == TokenIn {
			lparen, _ := p.next()
			if lparen.Kind != TokenLParen {
				x = &InExpr{
					X:      x,
					In:     op1.Span,
					Lparen: nullSpan(),
					Rparen: nullSpan(),
				}
				finalError = joinErrors(finalError, &parseError{
					source: p.source,
					span:   lparen.Span,
					err:    fmt.Errorf("expected '(', got %s", formatToken(p.source, lparen)),
				})
				return x, finalError
			}
			valParser := p.split(TokenRParen)
			vals, err := valParser.exprList()
			finalError = joinErrors(finalError, makeErrorOpaque(err), valParser.endSplit())
			rparen, _ := p.next()
			if rparen.Kind != TokenRParen {
				x = &InExpr{
					X:      x,
					In:     op1.Span,
					Lparen: lparen.Span,
					Vals:   vals,
					Rparen: nullSpan(),
				}
				finalError = joinErrors(finalError, &parseError{
					source: p.source,
					span:   lparen.Span,
					err:    fmt.Errorf("expected ')', got %s", formatToken(p.source, rparen)),
				})
				return x, finalError
			}

			x = &InExpr{
				X:      x,
				In:     op1.Span,
				Lparen: lparen.Span,
				Vals:   vals,
				Rparen: rparen.Span,
			}
			continue
		}

		y, err := p.unaryExpr()
		if err != nil {
			finalError = joinErrors(finalError, makeErrorOpaque(err))
		}

		// Resolve any higher precedence operators first.
		for {
			op2, ok := p.next()
			if !ok {
				break
			}
			p.prev()

			precedence2 := operatorPrecedence(op2.Kind)
			if precedence2 < 0 || precedence2 <= precedence1 {
				// Not a binary operator or below the precedence of the original operator.
				break
			}
			y, err = p.exprBinaryTrail(y, precedence1+1)
			if err != nil {
				finalError = joinErrors(finalError, makeErrorOpaque(err))
			}
		}

		x = &BinaryExpr{
			X:      x,
			OpSpan: op1.Span,
			Op:     op1.Kind,
			Y:      y,
		}
	}
}

func operatorPrecedence(op TokenKind) int {
	switch op {
	case TokenStar, TokenSlash, TokenMod:
		return 4
	case TokenPlus, TokenMinus:
		return 3
	case TokenEq, TokenNE, TokenLT, TokenLE, TokenGT, TokenGE,
		TokenCaseInsensitiveEq, TokenCaseInsensitiveNE, TokenIn:
		return 2
	case TokenAnd:
		return 1
	case TokenOr:
		return 0
	default:
		return -1
	}
}

func (p *parser) unaryExpr() (Expr, error) {
	tok, ok := p.next()
	if !ok {
		return nil, &parseError{
			source: p.source,
			span:   indexSpan(len(p.source)),
			err:    notFoundError{errors.New("expected expression, got EOF")},
		}
	}
	switch tok.Kind {
	case TokenPlus, TokenMinus:
		x, err := p.primaryExpr()
		err = makeErrorOpaque(err) // already parsed a symbol
		return &UnaryExpr{
			OpSpan: tok.Span,
			Op:     tok.Kind,
			X:      x,
		}, err
	default:
		p.prev()
		return p.primaryExpr()
	}
}

func (p *parser) primaryExpr() (Expr, error) {
	x, err := p.innerPrimaryExpr()
	if err != nil {
		return x, err
	}

	for {
		tok, ok := p.next()
		if !ok {
			return x, nil
		}
		switch tok.Kind {
		case TokenLBracket:
			idx := &IndexExpr{
				X:      x,
				Lbrack: tok.Span,
			}
			indexParser := p.split(TokenRBracket)
			var err error
			idx.Index, err = indexParser.expr()
			err = joinErrors(err, indexParser.endSplit())
			if tok, _ := p.next(); tok.Kind == TokenRBracket {
				idx.Rbrack = tok.Span
			} else {
				err = joinErrors(err, &parseError{
					source: p.source,
					span:   tok.Span,
					err:    fmt.Errorf("expected ']', got %s", formatToken(p.source, tok)),
				})
			}
			return idx, err
		default:
			p.prev()
			return x, nil
		}
	}
}

// innerPrimaryExpr parses the first element of a primary expression
// (i.e. a primary expression without any trailing index expressions).
func (p *parser) innerPrimaryExpr() (Expr, error) {
	tok, ok := p.next()
	if !ok {
		return nil, &parseError{
			source: p.source,
			span:   indexSpan(len(p.source)),
			err:    notFoundError{errors.New("expected expression, got EOF")},
		}
	}
	switch tok.Kind {
	case TokenNumber, TokenString:
		return &BasicLit{
			ValueSpan: tok.Span,
			Kind:      tok.Kind,
			Value:     tok.Value,
		}, nil
	case TokenHash:
		p.prev()
		return p.macro()
	case TokenIdentifier:
		// Look ahead for a dot-separated identifier.
		p.prev()
		id, err := p.qualifiedIdent()
		if err != nil {
			return id, err
		}
		if len(id.Parts) > 1 {
			// Dot-separated identifiers cannot be used as a function call.
			return id, nil
		}

		args, lparen, rparen, err := p.args()
		if isNotFound(err) {
			return id, nil
		}

		// Plain identifier may be followed by an opening parenthesis for a function call.
		return &CallExpr{
			Func: &Ident{
				Name:     tok.Value,
				NameSpan: tok.Span,
			},
			Lparen: lparen,
			Args:   args,
			Rparen: rparen,
		}, err
	case TokenQuotedIdentifier:
		p.prev()
		return p.qualifiedIdent()
	case TokenLParen:
		exprParser := p.split(TokenRParen)
		x, err := exprParser.expr()
		err = makeErrorOpaque(err) // already consumed a parenthesis
		err = joinErrors(err, exprParser.endSplit())

		endTok, _ := p.next()
		if endTok.Kind != TokenRParen {
			err = joinErrors(err, &parseError{
				source: p.source,
				span:   endTok.Span,
				err:    fmt.Errorf("expected ')', got %s", formatToken(p.source, endTok)),
			})
			return &ParenExpr{
				Lparen: tok.Span,
				X:      x,
				Rparen: nullSpan(),
			}, err
		}
		return &ParenExpr{
			Lparen: tok.Span,
			X:      x,
			Rparen: endTok.Span,
		}, err
	default:
		p.prev()
		return nil, &parseError{
			source: p.source,
			span:   tok.Span,
			err:    notFoundError{fmt.Errorf("expected expression, got %s", formatToken(p.source, tok))},
		}
	}
}

func (p *parser) macro() (*Macro, error) {
	tok, _ := p.next()
	if tok.Kind != TokenHash {
		p.prev()
		return nil, &parseError{
			source: p.source,
			span:   tok.Span,
			err:    notFoundError{fmt.Errorf("expected '#', got %s", formatToken(p.source, tok))},
		}
	}

	m := &Macro{
		Pipe:   nullSpan(),
		Hash:   tok.Span,
		Lparen: nullSpan(),
		Rparen: nullSpan(),
	}

	id, err := p.ident()
	if err != nil {
		return m, makeErrorOpaque(err)
	}

	m.Macro = id

	if id.Quoted {
		p.prev()
		return m, &parseError{
			source: p.source,
			span:   id.Span(),
			err:    errors.New("expected unquoted identifier for macro"),
		}
	}

	m.Args, m.Lparen, m.Rparen, err = p.args()
	if isNotFound(err) {
		err = nil
	}

	if err == nil && len(m.Args) == 0 && (m.Lparen.IsValid() || m.Rparen.IsValid()) {
		err = &parseError{
			source: p.source,
			span:   m.Span(),
			err:    errors.New("cannot use parenthesis for macro or #define without params"),
		}
	}

	return m, err
}

func (p *parser) args() (args []Expr, lparen, rparen Span, err error) {
	nextTok, _ := p.next()
	if nextTok.Kind != TokenLParen {
		p.prev()
		return nil, nullSpan(), nullSpan(), &parseError{
			source: p.source,
			span:   nextTok.Span,
			err:    notFoundError{fmt.Errorf("expected ')', got %s", formatToken(p.source, nextTok))},
		}
	}

	lparen = nextTok.Span

	argParser := p.split(TokenRParen)
	args, err = argParser.exprList()
	if isNotFound(err) {
		err = nil
	} else if err == nil {
		if tok, _ := argParser.next(); tok.Kind != TokenComma {
			argParser.prev()
		}
	}
	err = joinErrors(err, argParser.endSplit())

	rparen = nullSpan()
	if finalTok, _ := p.next(); finalTok.Kind == TokenRParen {
		rparen = finalTok.Span
	} else {
		p.prev()
		err = joinErrors(err, &parseError{
			source: p.source,
			span:   finalTok.Span,
			err:    fmt.Errorf("expected ')', got %s", formatToken(p.source, finalTok)),
		})
	}

	return
}

func (p *parser) ident() (*Ident, error) {
	tok, _ := p.next()
	if tok.Kind != TokenIdentifier && tok.Kind != TokenQuotedIdentifier {
		p.prev()
		return nil, &parseError{
			source: p.source,
			span:   indexSpan(len(p.source)),
			err:    notFoundError{fmt.Errorf("expected identifier, got %s", formatToken(p.source, tok))},
		}
	}
	return &Ident{
		Name:     tok.Value,
		NameSpan: tok.Span,
		Quoted:   tok.Kind == TokenQuotedIdentifier,
	}, nil
}

// qualifiedIdent parses one or more dot-separated identifiers.
func (p *parser) qualifiedIdent() (*QualifiedIdent, error) {
	id, err := p.ident()
	if err != nil {
		return nil, err
	}

	qid := id.AsQualified()
	for {
		tok, _ := p.next()
		if tok.Kind != TokenDot {
			p.prev()
			return qid, nil
		}
		sel, err := p.ident()
		if err != nil {
			return qid, makeErrorOpaque(err)
		}
		qid.Parts = append(qid.Parts, sel)
	}
}

// split advances the parser to right before the next token of the given kind,
// and returns a new parser that reads the tokens that were skipped over.
// It ignores tokens that are in parenthetical groups after the initial parse position.
// If no such token is found, split advances to EOF.
//
// For splitting by semicolon, see [*parser.splitSemi].
func (p *parser) split(search TokenKind) *parser {
	// stack is the list of expected closing parentheses/brackets.
	// When a closing parenthesis/bracket is encountered,
	// the stack is popped to include the first matching parenthesis/bracket.
	var stack []TokenKind

	start := p.pos
loop:
	for {
		tok, ok := p.next()
		if !ok {
			return &parser{
				source:    p.source,
				tokens:    p.tokens[start:],
				splitKind: search,
			}
		}

		switch tok.Kind {
		case TokenLParen, TokenLBracket:
			if search == tok.Kind {
				p.prev()
				break loop
			}
			switch tok.Kind {
			case TokenLParen:
				stack = append(stack, TokenRParen)
			case TokenLBracket:
				stack = append(stack, TokenRBracket)
			default:
				panic("unreachable")
			}
		case TokenRParen, TokenRBracket:
			if len(stack) > 0 {
				for len(stack) > 0 {
					k := stack[len(stack)-1]
					stack = stack[:len(stack)-1]
					if k == tok.Kind {
						break
					}
				}
			} else if search == tok.Kind {
				p.prev()
				break loop
			}
		case search:
			if len(stack) == 0 {
				p.prev()
				break loop
			}
		}
	}

	return &parser{
		source:    p.source,
		tokens:    p.tokens[start:p.pos],
		splitKind: search,
	}
}

// splitSemi advances the parser to right before the next semicolon,
// and returns a new parser that reads the tokens that were skipped over.
// If no semicolon is found, splitSemi advances to EOF.
func (p *parser) splitSemi() *parser {
	start := p.pos
	for {
		tok, ok := p.next()
		if !ok {
			return &parser{
				source:    p.source,
				tokens:    p.tokens[start:],
				splitKind: TokenSemi,
			}
		}
		if tok.Kind == TokenSemi {
			p.prev()
			return &parser{
				source:    p.source,
				tokens:    p.tokens[start:p.pos],
				splitKind: TokenSemi,
			}
		}
	}
}

func (p *parser) endSplit() error {
	if p.splitKind == 0 {
		// This is a bug, but treating as an error instead of panicing.
		return errors.New("internal error: endSplit called on non-split parser")
	}
	if p.pos < len(p.tokens) {
		var s string
		switch p.splitKind {
		case TokenPipe:
			s = "'|'"
		case TokenRParen:
			s = "')'"
		case TokenRBracket:
			s = "']'"
		default:
			s = p.splitKind.String()
		}
		tok := p.tokens[p.pos]
		return &parseError{
			source: p.source,
			span:   tok.Span,
			err:    fmt.Errorf("expected %s, got %s", s, formatToken(p.source, tok)),
		}
	}
	return nil
}

func (p *parser) next() (Token, bool) {
	if p.pos >= len(p.tokens) {
		p.pos = len(p.tokens) + 1 // Once we produce EOF, don't permit rewinding.
		return Token{
			Kind:  TokenError,
			Span:  indexSpan(len(p.source)),
			Value: "EOF",
		}, false
	}
	tok := p.tokens[p.pos]
	p.pos++
	return tok, true
}

func (p *parser) prev() {
	// Only allow rewinding to a previous token if it's in valid range,
	// and once we produce EOF, we will always produce EOF.
	if p.pos > 0 && p.pos <= len(p.tokens) {
		p.pos--
	}
}

func formatToken(source string, tok Token) string {
	if tok.Span.Start == len(source) && tok.Span.End == len(source) {
		return "EOF"
	}
	if tok.Span.Len() == 0 {
		if tok.Kind == TokenError {
			return "<scan error>"
		}
		return "''"
	}
	return "'" + spanString(source, tok.Span) + "'"
}

type parseError struct {
	source string
	span   Span
	err    error
}

func (e *parseError) Error() string {
	line, col := linecol(e.source, e.span.Start)
	return fmt.Sprintf("%d:%d: %s", line, col, e.err.Error())
}

func (e *parseError) Unwrap() error {
	return e.err
}

func linecol(source string, pos int) (line, col int) {
	line, col = 1, 1
	for _, c := range source[:pos] {
		switch c {
		case '\n':
			line++
			col = 1
		case '\t':
			const tabWidth = 8
			tabLoc := (col - 1) % tabWidth
			col += tabWidth - tabLoc
		default:
			col++
		}
	}
	return
}

func joinErrors(args ...error) error {
	var errorList []error
	for _, err := range args {
		if err == nil {
			continue
		}
		unwrapper, ok := err.(multiUnwrapper)
		if ok {
			errorList = append(errorList, unwrapper.Unwrap()...)
		} else {
			errorList = append(errorList, err)
		}
	}
	if len(errorList) == 0 {
		return nil
	}
	return errors.Join(errorList...)
}

// opaqueError is an error that does not unwrap its underlying error.
type opaqueError struct {
	error
}

func makeErrorOpaque(err error) error {
	switch e := err.(type) {
	case nil:
		return nil
	case *parseError:
		err2 := new(parseError)
		*err2 = *e
		err2.err = opaqueError{e.err}
		return err2
	case multiUnwrapper:
		errorList := slices.Clone(e.Unwrap())
		for i, err := range errorList {
			errorList[i] = opaqueError{err}
		}
		return errors.Join(errorList...)
	default:
		return opaqueError{err}
	}
}

// notFoundError is a sentinel for a production that did not parse anything.
type notFoundError struct {
	err error
}

func isNotFound(err error) bool {
	return errors.As(err, new(notFoundError))
}

func (e notFoundError) Error() string {
	return e.err.Error()
}

func (e notFoundError) Unwrap() error {
	return e.err
}

type multiUnwrapper interface {
	Unwrap() []error
}
