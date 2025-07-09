package parser

import (
	"errors"
	"fmt"
	"io"
	"slices"
	"strings"
)

func ParseNode(node string) (Node, error) {
	return parseNode(&parser{
		source: node,
		tokens: Scan(node),
	}, true)
}

func parseNode(p *parser, allowLet bool) (Node, error) {
	return firstParse(
		nodeParser(func() (*LetStatement, error) {
			if allowLet {
				return p.letStatement()
			}

			return nil, notFoundError{errors.New("disallowed")}
		}),
		nodeParser(func() (*TabularExpr, error) {
			t := *p
			t.split(TokenPipe)
			if _, ok := t.next(); !ok {
				return nil, notFoundError{io.EOF}
			}

			return p.tabularExpr()
		}),
		nodeParser(p.macro),
		operatorParser(p, (*parser).countOperator, "count"),
		operatorParser(p, (*parser).whereOperator, "where", "filter"),
		operatorParser(p, (*parser).sortOperator, "sort", "order"),
		operatorParser(p, (*parser).takeOperator, "take", "limit"),
		operatorParser(p, (*parser).topOperator, "top"),
		operatorParser(p, (*parser).joinOperator, "join"),
		operatorParser(p, (*parser).projectOperator, "project"),
		operatorParser(p, (*parser).extendOperator, "extend"),
		operatorParser(p, (*parser).summarizeOperator, "summarize"),
		operatorParser(p, (*parser).asOperator, "as"),
		operatorParser(p, (*parser).renderOperator, "render"),
		func() (Node, error) {
			return p.expr()
		},
	)
}

func nodeParser[T any, P interface {
	*T
	Node
}](p func() (P, error)) func() (Node, error) {
	return func() (Node, error) {
		v, err := p()
		if v == nil {
			return nil, err
		}
		return v, err
	}
}

func operatorParser[T any, P interface {
	*T
	TabularOperator
}](p *parser, pf func(*parser, Token, Token) (P, error), keywords ...string) func() (Node, error) {
	return nodeParser(func() (P, error) {
		tok, _ := p.next()
		if tok.Kind != TokenIdentifier || !slices.Contains(keywords, tok.Value) {
			p.prev()
			return nil, &parseError{
				source: p.source,
				span:   tok.Span,
				err:    notFoundError{fmt.Errorf("token %q does not match keywords %q", formatToken(p.source, tok), strings.Join(keywords, ","))},
			}
		}

		pipe := Token{
			Kind: TokenPipe,
			Span: Span{Start: tok.Span.Start - 2, End: tok.Span.Start - 1},
		}

		n, err := pf(p, pipe, tok)
		return n, makeErrorOpaque(err)
	})
}

var reserved = []string{
	"count",
	"join",
	"where",
	"filter",
	"sort",
	"order",
	"take",
	"limit",
	"top",
	"project",
	"extend",
	"summarize",
	"as",
	"render",
	"in",
	"by",
	"and",
	"or",
}
