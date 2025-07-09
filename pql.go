// Copyright 2024 RunReveal Inc.
// SPDX-License-Identifier: Apache-2.0

// Package pql provides a Pipeline Query Language that can be translated into SQL.
package pql

import (
	"errors"
	"fmt"
	"slices"
	"strings"
	"sync"

	"github.com/runreveal/pql/parser"
	"golang.org/x/exp/maps"
)

// Compile converts the given Pipeline Query Language statement
// into the equivalent SQL.
// This is equivalent to new(CompileOptions).Compile(source).
func Compile(source string) (string, error) {
	return ((*CompileOptions)(nil)).Compile(source)
}

// CompileOptions a set of optional parameters
// that configure compilation.
// nil is treated the same as the zero value.
type CompileOptions struct {
	// Parameters is a map of identifiers to SQL snippets to substitute in.
	// For example, a "foo": "$1" entry would replace unquoted "foo" identifiers
	// with "$1" in the resulting SQL.
	Parameters map[string]string
	Macros     map[string]Macro
}

type Macro func(macro *parser.Macro, parent parser.Node) (parser.Node, error)

func NewMacro[P parser.Node](nargs int, sub func(*parser.Macro, P) (parser.Node, error)) Macro {
	return func(macro *parser.Macro, parent parser.Node) (parser.Node, error) {
		if len(macro.Args) != nargs {
			return nil, fmt.Errorf("expected %d args, got %d", nargs, len(macro.Args))
		}

		p, ok := parent.(P)
		if !ok {
			return nil, fmt.Errorf("expected %T parent, got %T", p, parent)
		}

		return sub(macro, p)
	}
}

// Compile converts the given Pipeline Query Language statement
// into the equivalent SQL.
func (opts *CompileOptions) Compile(source string) (string, error) {
	stmts, err := parser.Parse(source)
	if err != nil {
		return "", err
	}
	var expr *parser.TabularExpr
	scope := make(map[string]string)
	macros := make(map[string]Macro)
	if opts != nil {
		maps.Copy(scope, opts.Parameters)
		maps.Copy(macros, opts.Macros)
	}
	for i := 0; i < len(stmts); {
		switch stmt := stmts[i].(type) {
		case *parser.TabularExpr:
			if expr != nil {
				return "", &compileError{
					source: source,
					span:   stmt.Span(),
					err:    fmt.Errorf("batch queries not supported"),
				}
			}
			expr = stmt
		case *parser.LetStatement:
			if expr != nil {
				// Skip let statements after the query:
				// they should not be in scope.
				continue
			}
			ctx := &exprContext{
				source: source,
				scope:  scope,
				mode:   letExprMode,
				macros: macros,
			}
			sb := new(strings.Builder)
			if err := writeExpressionMaybeParen(ctx, sb, stmt.X, stmt); err != nil {
				return "", err
			}
			scope[stmt.Name.Name] = sb.String()
		case *parser.Macro:
			s, err := macro[parser.Statement](&exprContext{
				source: source,
				scope:  scope,
				macros: macros,
			}, stmt, nil)
			if err != nil {
				return "", err
			}

			stmts[i] = s

			continue
		default:
			return "", &compileError{
				source: source,
				span:   stmt.Span(),
				err:    fmt.Errorf("unhandled %T statement", stmt),
			}
		}

		i++
	}
	if expr == nil {
		return "", fmt.Errorf("missing tabular queries")
	}

	subqueries, err := splitQueries(nil, source, macros, expr)
	if err != nil {
		return "", err
	}

	sb := new(strings.Builder)
	ctes := subqueries[:len(subqueries)-1]
	query := subqueries[len(subqueries)-1]
	ctx := &exprContext{
		source: source,
		scope:  scope,
		macros: macros,
	}
	if len(ctes) > 0 {
		sb.WriteString("WITH ")
		for i, sub := range ctes {
			quoteIdentifier(sb, sub.name)
			sb.WriteString(" AS (")
			if err := sub.write(ctx, sb); err != nil {
				return "", err
			}
			sb.WriteString(")")
			if i < len(ctes)-1 {
				sb.WriteString(",\n     ")
			} else {
				sb.WriteString("\n")
			}
		}
	}
	if err := query.write(ctx, sb); err != nil {
		return "", err
	}
	sb.WriteString(";")
	return sb.String(), nil
}

type subquery struct {
	name      string
	sourceSQL string

	op   parser.TabularOperator
	sort *parser.SortOperator
	take *parser.TakeOperator
}

// splitQueries appends queries to dst that represent the given tabular expression.
// The last element of the returned slice will be the query that represents the full expression.
func splitQueries(dst []*subquery, source string, macros map[string]Macro, expr *parser.TabularExpr) ([]*subquery, error) {
	dstStart := len(dst)
	var lastSubquery *subquery
	for i := 0; i < len(expr.Operators); i++ {
		switch op := expr.Operators[i].(type) {
		case *parser.Macro:
			n, err := macro[parser.TabularOperator](&exprContext{source: source, macros: macros}, op, expr)
			if err != nil {
				return nil, err
			}
			expr.Operators[i] = n
			i--
		case *parser.AsOperator:
			var err error
			lastSubquery, err = chainSubquery(dst, dstStart, expr.Source)
			if err != nil {
				return nil, err
			}
			lastSubquery.name = op.Name.Name
			// AsOperator gets treated basically the same as nil,
			// but won't permit anything to be attached.
			lastSubquery.op = op
			dst = append(dst, lastSubquery)
		case *parser.SortOperator:
			if lastSubquery == nil || !canAttachSort(lastSubquery.op) || lastSubquery.sort != nil || lastSubquery.take != nil {
				var err error
				lastSubquery, err = chainSubquery(dst, dstStart, expr.Source)
				if err != nil {
					return nil, err
				}
				dst = append(dst, lastSubquery)
			}
			lastSubquery.sort = op
		case *parser.TakeOperator:
			if lastSubquery == nil || !canAttachSort(lastSubquery.op) || lastSubquery.take != nil {
				var err error
				lastSubquery, err = chainSubquery(dst, dstStart, expr.Source)
				if err != nil {
					return nil, err
				}
				dst = append(dst, lastSubquery)
			}
			lastSubquery.take = op
		case *parser.TopOperator:
			if lastSubquery == nil || !canAttachSort(lastSubquery.op) || lastSubquery.sort != nil || lastSubquery.take != nil {
				var err error
				lastSubquery, err = chainSubquery(dst, dstStart, expr.Source)
				if err != nil {
					return nil, err
				}
				dst = append(dst, lastSubquery)
			}
			lastSubquery.sort = &parser.SortOperator{
				Pipe:    op.Pipe,
				Keyword: op.Keyword,
				Terms:   []*parser.SortTerm{op.Col},
			}
			lastSubquery.take = &parser.TakeOperator{
				Pipe:     op.Pipe,
				Keyword:  op.Keyword,
				RowCount: op.RowCount,
			}
		case *parser.JoinOperator:
			leftSubquery := len(dst) - 1

			var err error

			if m := op.Macro; m != nil {
				op.Right, err = macro[*parser.TabularExpr](&exprContext{source: source, macros: macros}, m, op)
				if err != nil {
					return nil, err
				}
			}

			dst, err = splitQueries(dst, source, macros, op.Right)
			if err != nil {
				return nil, err
			}
			lastSubquery = dst[len(dst)-1]

			flavorName := "innerunique"
			if op.Flavor != nil {
				flavorName = op.Flavor.Name
			}

			joinSource := new(strings.Builder)
			if flavorName == "innerunique" {
				joinSource.WriteString("(SELECT DISTINCT * FROM ")
			}
			if leftSubquery >= dstStart {
				quoteIdentifier(joinSource, dst[leftSubquery].name)
			} else {
				if err := dataSourceSQL(joinSource, expr.Source); err != nil {
					return nil, err
				}
			}
			if flavorName == "innerunique" {
				joinSource.WriteString(")")
			}
			joinSource.WriteString(` AS "` + leftJoinTableAlias + `"`)

			switch flavorName {
			case "inner", "innerunique":
				joinSource.WriteString(" JOIN ")
			case "leftouter":
				joinSource.WriteString(" LEFT JOIN ")
			default:
				return nil, &compileError{
					source: source,
					span:   op.Flavor.Span(),
					err:    fmt.Errorf("unhandled join type %q", flavorName),
				}
			}
			quoteIdentifier(joinSource, lastSubquery.name)

			joinSource.WriteString(` AS "` + rightJoinTableAlias + `" ON `)
			joinCtx := &exprContext{
				source: source,
				mode:   joinExprMode,
				macros: macros,
			}
			if err := writeExpression(joinCtx, joinSource, buildJoinCondition(op.Conditions), op); err != nil {
				return nil, err
			}

			lastSubquery = &subquery{
				name:      subqueryName(len(dst)),
				sourceSQL: joinSource.String(),
			}
			dst = append(dst, lastSubquery)
		default:
			var err error
			lastSubquery, err = chainSubquery(dst, dstStart, expr.Source)
			if err != nil {
				return nil, err
			}
			lastSubquery.op = op
			dst = append(dst, lastSubquery)
		}
	}

	if len(dst) == dstStart {
		// Ensure that we add at least one subquery.
		var err error
		lastSubquery, err = chainSubquery(dst, dstStart, expr.Source)
		if err != nil {
			return nil, err
		}
		dst = append(dst, lastSubquery)
	}

	return dst, nil
}

// chainSubquery returns a new subquery
// that either reads from the previous subquery
// or from the data source if there is no previous subquery.
func chainSubquery(dst []*subquery, dstStart int, src parser.TabularDataSource) (*subquery, error) {
	sub := &subquery{
		name: subqueryName(len(dst)),
	}
	sb := new(strings.Builder)
	if len(dst) > dstStart {
		quoteIdentifier(sb, dst[len(dst)-1].name)
	} else {
		if err := dataSourceSQL(sb, src); err != nil {
			return nil, err
		}
	}
	sub.sourceSQL = sb.String()
	return sub, nil
}

func subqueryName(i int) string {
	return fmt.Sprintf("__subquery%d", i)
}

// canAttachSort reports whether the given operator's subquery can have a sort clause attached.
// This becomes significant for operators like "project"
// because they change the identifiers in scope.
func canAttachSort(op parser.TabularOperator) bool {
	switch op.(type) {
	case *parser.ProjectOperator, *parser.SummarizeOperator, *parser.AsOperator:
		return false
	case *parser.RenderOperator:
		return false
	default:
		return true
	}
}

const (
	leftJoinTableAlias  = "$left"
	rightJoinTableAlias = "$right"
)

func buildJoinCondition(conds []parser.Expr) parser.Expr {
	if len(conds) == 0 {
		return (&parser.Ident{Name: "true"}).AsQualified()
	}
	x := rewriteSimpleJoinCondition(conds[0])
	for _, y := range conds[1:] {
		x = &parser.BinaryExpr{
			X:  x,
			Op: parser.TokenAnd,
			Y:  rewriteSimpleJoinCondition(y),
		}
	}
	return x
}

func rewriteSimpleJoinCondition(c parser.Expr) parser.Expr {
	id, ok := c.(*parser.QualifiedIdent)
	if !ok || len(id.Parts) != 1 || id.Parts[0].Quoted || builtinIdentifiers[id.Parts[0].Name] != "" {
		return c
	}
	return &parser.BinaryExpr{
		X: &parser.QualifiedIdent{
			Parts: []*parser.Ident{
				{Name: leftJoinTableAlias},
				id.Parts[0],
			},
		},
		Op: parser.TokenEq,
		Y: &parser.QualifiedIdent{
			Parts: []*parser.Ident{
				{Name: rightJoinTableAlias},
				id.Parts[0],
			},
		},
	}
}

func hasJoinTerms(x parser.Expr) (left, right bool) {
	parser.Walk(x, func(n parser.Node) bool {
		if n, ok := n.(*parser.Ident); ok {
			switch n.Name {
			case leftJoinTableAlias:
				left = true
			case rightJoinTableAlias:
				right = true
			}
		}
		return true
	})
	return
}

func expandProjectionColumn(ctx *exprContext, c *parser.ProjectColumn, p *parser.ProjectOperator) (*parser.ProjectColumn, []*parser.ProjectColumn, error) {
	if c.Macro == nil {
		return c, nil, nil
	}

	var n parser.Node
	var err error

	if c.X != nil {
		n, err = macro[*parser.QualifiedIdent](ctx, c.Macro, p)
	} else {
		n, err = macro[parser.Node](ctx, c.Macro, p)
	}

	if err != nil {
		return nil, nil, err
	}

	switch v := n.(type) {
	case *parser.QualifiedIdent:
		if len(v.Parts) > 1 {
			return nil, nil, &compileError{
				source: ctx.source,
				span:   c.Macro.Span(),
				err:    errors.New("can't substitute projection column name macro for qualified column with parts"),
			}
		}

		c.Macro = nil
		c.Name = v.Parts[0]

		return c, nil, nil
	case *parser.ProjectColumn:
		return expandProjectionColumn(ctx, v, p)
	case *parser.ProjectOperator:
		if len(v.Cols) == 0 {
			return nil, nil, nil
		}

		c, rest, err := expandProjectionColumn(ctx, v.Cols[0], p)

		return c, append(rest, v.Cols[1:]...), err
	default:
		return nil, nil, &compileError{
			source: ctx.source,
			span:   c.Macro.Span(),
			err:    fmt.Errorf("for macro %q: unsupported substitution type %T in project operator", c.Macro.Macro.Name, v),
		}
	}
}

func expandExtendColumn(ctx *exprContext, c *parser.ExtendColumn, e *parser.ExtendOperator) (*parser.ExtendColumn, []*parser.ExtendColumn, error) {
	if c.Macro == nil {
		return c, nil, nil
	}

	n, err := macro[parser.Node](ctx, c.Macro, e)
	if err != nil {
		return nil, nil, err
	}

	switch v := n.(type) {
	case *parser.ExtendColumn:
		return expandExtendColumn(ctx, v, e)
	case *parser.ExtendOperator:
		if len(v.Cols) == 0 {
			return nil, nil, &compileError{
				source: ctx.source,
				span:   c.Macro.Span(),
				err:    fmt.Errorf("for macro %q: expanded to no columns in extend operator", c.Macro.Macro.Name),
			}
		}

		c, rest, err := expandExtendColumn(ctx, v.Cols[0], e)

		return c, append(rest, v.Cols[1:]...), err
	default:
		return nil, nil, &compileError{
			source: ctx.source,
			span:   c.Macro.Span(),
			err:    fmt.Errorf("for macro %q: unsupported substitution type %T in extend operator", c.Macro.Macro.Name, v),
		}
	}
}

func expandSortTerms(ctx *exprContext, t *parser.SortTerm, o *parser.SortOperator) (*parser.SortTerm, []*parser.SortTerm, error) {
	if t.Macro == nil {
		return t, nil, nil
	}

	n, err := macro[parser.Node](ctx, t.Macro, o)
	if err != nil {
		return nil, nil, err
	}

	switch v := n.(type) {
	case *parser.SortTerm:
		if t.X != nil {
			v.X = t.X
		}

		return expandSortTerms(ctx, v, o)
	case *parser.SortOperator:
		if len(v.Terms) == 0 {
			return nil, nil, nil
		}

		if t.X != nil {
			if len(v.Terms) > 1 {
				return nil, nil, &compileError{
					source: ctx.source,
					span:   t.Macro.Span(),
					err:    fmt.Errorf("for macro %q: attempt substituion of sort term with expr with multiple sort terms", t.Macro.Macro.Name),
				}
			}
			nt := v.Terms[0]
			nt.X = t.X
			return expandSortTerms(ctx, nt, o)
		}

		t, rest, err := expandSortTerms(ctx, v.Terms[0], o)

		return t, append(rest, v.Terms[1:]...), err
	default:
		return nil, nil, &compileError{
			source: ctx.source,
			span:   t.Macro.Span(),
			err:    fmt.Errorf("for macro %q: unsupported substitution type %T in sort operator", t.Macro.Macro.Name, v),
		}
	}
}

func (sub *subquery) write(ctx *exprContext, sb *strings.Builder) error {
	switch op := sub.op.(type) {
	case nil, *parser.AsOperator:
		sb.WriteString("SELECT * FROM ")
		sb.WriteString(sub.sourceSQL)
	case *parser.ProjectOperator:
		sb.WriteString("SELECT ")
		var written bool
		for i := 0; i < len(op.Cols); i++ {
			col, rest, err := expandProjectionColumn(ctx, op.Cols[i], op)
			if err != nil {
				return err
			}

			if col == nil {
				continue
			}

			op.Cols = slices.Insert(op.Cols, i+1, rest...)

			if written {
				sb.WriteString(", ")
			} else {
				written = true
			}

			if col.X == nil {
				if err := writeExpression(ctx, sb, col.Name.AsQualified(), col); err != nil {
					return err
				}
			} else {
				if err := writeExpression(ctx, sb, col.X, col); err != nil {
					return err
				}
			}
			sb.WriteString(" AS ")
			quoteIdentifier(sb, col.Name.Name)
		}
		sb.WriteString(" FROM ")
		sb.WriteString(sub.sourceSQL)
	case *parser.ExtendOperator:
		sb.WriteString("SELECT *")
		for i := 0; i < len(op.Cols); i++ {
			col, rest, err := expandExtendColumn(ctx, op.Cols[i], op)
			if err != nil {
				return err
			}

			op.Cols = slices.Insert(op.Cols, i+1, rest...)

			sb.WriteString(", ")
			if err := writeExpression(ctx, sb, col.X, col); err != nil {
				return err
			}
			if col.X == nil {
				if err := writeExpression(ctx, sb, col.Name.AsQualified(), col); err != nil {
					return err
				}
			}
			sb.WriteString(" AS ")
			if col.Name != nil {
				quoteIdentifier(sb, col.Name.Name)
			} else {
				span := col.X.Span()
				quoteIdentifier(sb, ctx.source[span.Start:span.End])
			}
		}
		sb.WriteString(" FROM ")
		sb.WriteString(sub.sourceSQL)
	case *parser.SummarizeOperator:
		sb.WriteString("SELECT ")
		for i, col := range op.GroupBy {
			if i > 0 {
				sb.WriteString(", ")
			}
			// TODO(maybe): Verify that these are aggregation function calls?
			if err := writeExpression(ctx, sb, col.X, col); err != nil {
				return err
			}
			sb.WriteString(" AS ")
			if col.Name != nil {
				quoteIdentifier(sb, col.Name.Name)
			} else {
				span := col.X.Span()
				quoteIdentifier(sb, ctx.source[span.Start:span.End])
			}
		}
		for i, col := range op.Cols {
			if i > 0 || len(op.GroupBy) > 0 {
				sb.WriteString(", ")
			}
			if err := writeExpression(ctx, sb, col.X, col); err != nil {
				return err
			}
			sb.WriteString(" AS ")
			if col.Name != nil {
				quoteIdentifier(sb, col.Name.Name)
			} else {
				span := col.X.Span()
				quoteIdentifier(sb, ctx.source[span.Start:span.End])
			}
		}

		sb.WriteString(" FROM ")
		sb.WriteString(sub.sourceSQL)

		if len(op.GroupBy) > 0 {
			sb.WriteString(" GROUP BY ")
			for i, col := range op.GroupBy {
				if i > 0 {
					sb.WriteString(", ")
				}
				if err := writeExpression(ctx, sb, col.X, col); err != nil {
					return err
				}
			}
		}
	case *parser.WhereOperator:
		sb.WriteString("SELECT * FROM ")
		sb.WriteString(sub.sourceSQL)
		sb.WriteString(" WHERE ")
		if err := writeExpression(ctx, sb, op.Predicate, op); err != nil {
			return err
		}
	case *parser.CountOperator:
		sb.WriteString(`SELECT COUNT(*) AS "count()" FROM `)
		sb.WriteString(sub.sourceSQL)
	case *parser.RenderOperator:
		// First, write the source data
		sb.WriteString("SELECT *,\n")
		// Then add our render-specific metadata columns
		sb.WriteString("    '")
		sb.WriteString(op.ChartType.Name)
		sb.WriteString("' as \"render_type\"")

		// Add render properties with standardized prefixes
		for _, prop := range op.Props {
			sb.WriteString(",\n    ")
			// Quote all values as strings since they're instructions for the renderer
			sb.WriteString("'")
			if lit, ok := prop.Value.(*parser.BasicLit); ok {
				// Use the literal value directly
				sb.WriteString(lit.Value)
			} else if id, ok := prop.Value.(*parser.QualifiedIdent); ok {
				// Use the identifier name
				sb.WriteString(id.Parts[0].Name)
			}
			sb.WriteString("' as \"render_prop_")
			sb.WriteString(prop.Name.Name)
			sb.WriteString("\"")
		}

		sb.WriteString("\nFROM ")
		sb.WriteString(sub.sourceSQL)
	default:
		fmt.Fprintf(sb, "SELECT NULL /* unsupported operator %T */", op)
		return nil
	}

	if sub.sort != nil {
		var written bool
		for i := 0; i < len(sub.sort.Terms); i++ {
			term, rest, err := expandSortTerms(ctx, sub.sort.Terms[i], sub.sort)
			if err != nil {
				return err
			}

			if term == nil {
				continue
			}

			sub.sort.Terms = slices.Insert(sub.sort.Terms, i+1, rest...)

			if written {
				sb.WriteString(", ")
			} else {
				sb.WriteString(" ORDER BY ")
				written = true
			}

			if err := writeExpression(ctx, sb, term.X, term); err != nil {
				return err
			}
			if term.Asc {
				sb.WriteString(" ASC")
			} else {
				sb.WriteString(" DESC")
			}
			if term.NullsFirst {
				sb.WriteString(" NULLS FIRST")
			} else {
				sb.WriteString(" NULLS LAST")
			}
		}
	}

	if sub.take != nil {
		sb.WriteString(" LIMIT ")
		if err := writeExpression(ctx, sb, sub.take.RowCount, sub.take); err != nil {
			return err
		}
	}

	return nil
}

func dataSourceSQL(sb *strings.Builder, src parser.TabularDataSource) error {
	switch src := src.(type) {
	case *parser.TableRef:
		quoteIdentifier(sb, src.Table.Name)
		return nil
	default:
		return fmt.Errorf("unhandled data source %T", src)
	}
}

func quoteIdentifier(sb *strings.Builder, name string) {
	const quoteEscape = `""`
	sb.Grow(len(name) + strings.Count(name, `"`)*(len(quoteEscape)-1) + len(`""`))

	sb.WriteString(`"`)
	for _, b := range []byte(name) {
		if b == '"' {
			sb.WriteString(quoteEscape)
		} else {
			sb.WriteByte(b)
		}
	}
	sb.WriteString(`"`)
}

var builtinIdentifiers = map[string]string{
	"true":  "TRUE",
	"false": "FALSE",
	"null":  "NULL",
}

var binaryOps = map[parser.TokenKind]string{
	parser.TokenAnd:   "AND",
	parser.TokenOr:    "OR",
	parser.TokenPlus:  "+",
	parser.TokenMinus: "-",
	parser.TokenStar:  "*",
	parser.TokenSlash: "/",
	parser.TokenMod:   "%",
	parser.TokenLT:    "<",
	parser.TokenLE:    "<=",
	parser.TokenGT:    ">",
	parser.TokenGE:    ">=",
}

type exprMode int

const (
	defaultExprMode exprMode = iota
	joinExprMode
	letExprMode
)

type exprContext struct {
	source string
	scope  map[string]string
	mode   exprMode
	macros map[string]Macro
}

func macro[T parser.Node](ctx *exprContext, m *parser.Macro, parent parser.Node) (T, error) {
	span := m.Span()

	for {
		sub, ok := ctx.macros[m.Macro.Name]
		if !ok {
			return *new(T), &compileError{
				source: ctx.source,
				span:   span,
				err:    fmt.Errorf("unhandled macro %q", m.Macro.Name),
			}
		}

		n, err := sub(m, parent)
		if err != nil {
			return *new(T), &compileError{
				source: ctx.source,
				span:   span,
				err:    fmt.Errorf("substitute macro %q: %w", m.Macro.Name, err),
			}
		}

		switch t := n.(type) {
		case T:
			return t, nil
		case *parser.Macro:
			m = t
			continue
		default:
			return *new(T), &compileError{
				source: ctx.source,
				span:   span,
				err:    fmt.Errorf("expected macro %q to be substituted for %T, got %T", m.Macro.Name, *new(T), n),
			}
		}
	}
}

func writeExpression(ctx *exprContext, sb *strings.Builder, x parser.Expr, parent parser.Node) error {
	// Unwrap any parentheses.
	// We manually insert parentheses as needed.
	for {
		p, ok := x.(*parser.ParenExpr)
		if !ok {
			break
		}
		x = p.X
	}

	switch x := x.(type) {
	case *parser.QualifiedIdent:
		if len(x.Parts) == 1 {
			part := x.Parts[0]
			if !part.Quoted {
				if sql, ok := ctx.scope[part.Name]; ok {
					sb.WriteString(sql)
					return nil
				}
				if sql, ok := builtinIdentifiers[part.Name]; ok {
					sb.WriteString(sql)
					return nil
				}
				if ctx.mode == letExprMode {
					return &compileError{
						source: ctx.source,
						span:   part.NameSpan,
						err:    fmt.Errorf("unknown identifier %s in let expression", part.Name),
					}
				}
			} else if ctx.mode == letExprMode {
				return &compileError{
					source: ctx.source,
					span:   part.NameSpan,
					err:    fmt.Errorf("quoted identifier not permitted in let expression"),
				}
			}
		} else if ctx.mode == letExprMode {
			return &compileError{
				source: ctx.source,
				span:   x.Span(),
				err:    fmt.Errorf("qualified identifier not permitted in let expression"),
			}
		}

		for i, part := range x.Parts {
			if i > 0 {
				sb.WriteString(".")
			}
			if !part.Quoted && (part.Name == leftJoinTableAlias || part.Name == rightJoinTableAlias) && ctx.mode != joinExprMode {
				return &compileError{
					source: ctx.source,
					span:   part.NameSpan,
					err:    fmt.Errorf("%s used in non-join context", part.Name),
				}
			}
			quoteIdentifier(sb, part.Name)
		}
	case *parser.BasicLit:
		switch x.Kind {
		case parser.TokenNumber:
			sb.WriteString(x.Value)
		case parser.TokenString:
			quoteSQLString(sb, x.Value)
		default:
			fmt.Fprintf(sb, "NULL /* unhandled %s literal */", x.Kind)
		}
	case *parser.UnaryExpr:
		switch x.Op {
		case parser.TokenPlus:
			sb.WriteString("+")
		case parser.TokenMinus:
			sb.WriteString("-")
		default:
			fmt.Fprintf(sb, "/* unhandled %s unary op */ ", x.Op)
		}
		if err := writeExpressionMaybeParen(ctx, sb, x.X, x); err != nil {
			return err
		}
	case *parser.BinaryExpr:
		switch x.Op {
		case parser.TokenEq:
			if ctx.mode == joinExprMode {
				xl, xr := hasJoinTerms(x.X)
				yl, yr := hasJoinTerms(x.Y)
				if (xl || yl) && (xr || yr) {
					// Special case: Clickhouse only supports basic equality when comparing left and right columns in a JOIN.
					// Drop the coalesce if we might be doing that.
					// https://clickhouse.com/docs/en/sql-reference/statements/select/join#on-section-conditions

					if err := writeExpressionMaybeParen(ctx, sb, x.X, x); err != nil {
						return err
					}
					sb.WriteString(" = ")
					if err := writeExpressionMaybeParen(ctx, sb, x.Y, x); err != nil {
						return err
					}
					return nil
				}
			}

			sb.WriteString("coalesce(")
			if err := writeExpressionMaybeParen(ctx, sb, x.X, x); err != nil {
				return err
			}
			sb.WriteString(" = ")
			if err := writeExpressionMaybeParen(ctx, sb, x.Y, x); err != nil {
				return err
			}
			sb.WriteString(", FALSE)")
		case parser.TokenNE:
			sb.WriteString("coalesce(")
			if err := writeExpressionMaybeParen(ctx, sb, x.X, x); err != nil {
				return err
			}
			sb.WriteString(" <> ")
			if err := writeExpressionMaybeParen(ctx, sb, x.Y, x); err != nil {
				return err
			}
			sb.WriteString(", FALSE)")
		case parser.TokenCaseInsensitiveEq:
			sb.WriteString("lower(")
			if err := writeExpression(ctx, sb, x.X, x); err != nil {
				return err
			}
			sb.WriteString(") = lower(")
			if err := writeExpression(ctx, sb, x.Y, x); err != nil {
				return err
			}
			sb.WriteString(")")
		case parser.TokenCaseInsensitiveNE:
			sb.WriteString("lower(")
			if err := writeExpression(ctx, sb, x.X, x); err != nil {
				return err
			}
			sb.WriteString(") <> lower(")
			if err := writeExpression(ctx, sb, x.Y, x); err != nil {
				return err
			}
			sb.WriteString(")")
		default:
			if sqlOp, ok := binaryOps[x.Op]; ok {
				if err := writeExpressionMaybeParen(ctx, sb, x.X, x); err != nil {
					return err
				}
				sb.WriteString(" ")
				sb.WriteString(sqlOp)
				sb.WriteString(" ")
				if err := writeExpressionMaybeParen(ctx, sb, x.Y, x); err != nil {
					return err
				}
			} else {
				fmt.Fprintf(sb, "NULL /* unhandled %s binary op */ ", x.Op)
			}
		}
	case *parser.InExpr:
		if err := writeExpressionMaybeParen(ctx, sb, x.X, x); err != nil {
			return err
		}
		sb.WriteString(" IN (")
		for i, y := range x.Vals {
			if i > 0 {
				sb.WriteString(", ")
			}
			if err := writeExpressionMaybeParen(ctx, sb, y, x); err != nil {
				return err
			}
		}
		sb.WriteString(")")
	case *parser.IndexExpr:
		if err := writeExpressionMaybeParen(ctx, sb, x.X, x); err != nil {
			return err
		}
		sb.WriteString("[")
		if err := writeExpression(ctx, sb, x.Index, x); err != nil {
			return err
		}
		sb.WriteString("]")
	case *parser.CallExpr:
		if f := initKnownFunctions()[x.Func.Name]; f != nil {
			if err := f.write(ctx, sb, x); err != nil {
				return err
			}
		} else {
			sb.WriteString(x.Func.Name)
			sb.WriteString("(")
			for i, arg := range x.Args {
				if i > 0 {
					sb.WriteString(", ")
				}
				if err := writeExpression(ctx, sb, arg, x); err != nil {
					return err
				}
			}
			sb.WriteString(")")
		}
	case *parser.Macro:
		expr, err := macro[parser.Expr](ctx, x, parent)
		if err != nil {
			return err
		}

		return writeExpressionMaybeParen(ctx, sb, expr, parent)
	default:
		fmt.Fprintf(sb, "NULL /* unhandled %T expression */", x)
	}
	return nil
}

// writeExpressionMaybeParen writes an expression to sb,
// surrounding it with parentheses if sufficiently complex.
func writeExpressionMaybeParen(ctx *exprContext, sb *strings.Builder, x parser.Expr, parent parser.Node) error {
	for {
		p, ok := x.(*parser.ParenExpr)
		if !ok {
			break
		}
		x = p.X
	}

	switch x := x.(type) {
	case *parser.QualifiedIdent, *parser.UnaryExpr, *parser.BasicLit:
		return writeExpression(ctx, sb, x, parent)
	case *parser.CallExpr:
		if f := initKnownFunctions()[x.Func.Name]; f == nil || !f.needsParens {
			return writeExpression(ctx, sb, x, parent)
		}
	}

	sb.WriteString("(")
	if err := writeExpression(ctx, sb, x, parent); err != nil {
		return err
	}
	sb.WriteString(")")
	return nil
}

type functionRewrite struct {
	write func(ctx *exprContext, sb *strings.Builder, x *parser.CallExpr) error

	// needsParens should be true if the output SQL can have a binary operator.
	needsParens bool
}

var knownFunctions struct {
	init sync.Once
	m    map[string]*functionRewrite
}

func initKnownFunctions() map[string]*functionRewrite {
	knownFunctions.init.Do(func() {
		knownFunctions.m = map[string]*functionRewrite{
			"count":     {write: writeCountFunction},
			"countif":   {write: writeCountIfFunction},
			"iif":       {write: writeIfFunction, needsParens: true},
			"iff":       {write: writeIfFunction, needsParens: true},
			"isnotnull": {write: writeIsNotNullFunction, needsParens: true},
			"isnull":    {write: writeIsNullFunction, needsParens: true},
			"not":       {write: writeNotFunction},
			"now":       {write: writeNowFunction},
			"strcat":    {write: writeStrcatFunction, needsParens: true},
			"tolower":   {write: writeToLowerFunction, needsParens: true},
			"toupper":   {write: writeToUpperFunction, needsParens: true},
		}
	})
	return knownFunctions.m
}

func writeNotFunction(ctx *exprContext, sb *strings.Builder, x *parser.CallExpr) error {
	if len(x.Args) != 1 {
		return &compileError{
			source: ctx.source,
			span: parser.Span{
				Start: x.Lparen.End,
				End:   x.Rparen.Start,
			},
			err: fmt.Errorf("not(x) takes a single argument (got %d)", len(x.Args)),
		}
	}
	sb.WriteString("NOT ")
	if err := writeExpressionMaybeParen(ctx, sb, x.Args[0], x); err != nil {
		return err
	}
	return nil
}

func writeNowFunction(ctx *exprContext, sb *strings.Builder, x *parser.CallExpr) error {
	if len(x.Args) != 0 {
		return &compileError{
			source: ctx.source,
			span: parser.Span{
				Start: x.Lparen.End,
				End:   x.Rparen.Start,
			},
			err: fmt.Errorf("now()) takes a no arguments (got %d)", len(x.Args)),
		}
	}
	sb.WriteString("CURRENT_TIMESTAMP")
	return nil
}

func writeIsNullFunction(ctx *exprContext, sb *strings.Builder, x *parser.CallExpr) error {
	if len(x.Args) != 1 {
		return &compileError{
			source: ctx.source,
			span: parser.Span{
				Start: x.Lparen.End,
				End:   x.Rparen.Start,
			},
			err: fmt.Errorf("isnull(x) takes a single argument (got %d)", len(x.Args)),
		}
	}
	if err := writeExpressionMaybeParen(ctx, sb, x.Args[0], x); err != nil {
		return err
	}
	sb.WriteString(" IS NULL")
	return nil
}

func writeIsNotNullFunction(ctx *exprContext, sb *strings.Builder, x *parser.CallExpr) error {
	if len(x.Args) != 1 {
		return &compileError{
			source: ctx.source,
			span: parser.Span{
				Start: x.Lparen.End,
				End:   x.Rparen.Start,
			},
			err: fmt.Errorf("isnotnull(x) takes a single argument (got %d)", len(x.Args)),
		}
	}
	if err := writeExpressionMaybeParen(ctx, sb, x.Args[0], x); err != nil {
		return err
	}
	sb.WriteString(" IS NOT NULL")
	return nil
}

func writeStrcatFunction(ctx *exprContext, sb *strings.Builder, x *parser.CallExpr) error {
	if len(x.Args) == 0 {
		return &compileError{
			source: ctx.source,
			span: parser.Span{
				Start: x.Lparen.End,
				End:   x.Rparen.Start,
			},
			err: fmt.Errorf("strcat(x) takes least one argument"),
		}
	}
	if err := writeExpressionMaybeParen(ctx, sb, x.Args[0], x); err != nil {
		return err
	}
	for _, arg := range x.Args[1:] {
		sb.WriteString(" || ")
		if err := writeExpressionMaybeParen(ctx, sb, arg, x); err != nil {
			return err
		}
	}
	return nil
}

func writeCountFunction(ctx *exprContext, sb *strings.Builder, x *parser.CallExpr) error {
	if len(x.Args) != 0 {
		return &compileError{
			source: ctx.source,
			span: parser.Span{
				Start: x.Lparen.End,
				End:   x.Rparen.Start,
			},
			err: fmt.Errorf("count() takes no arguments (got %d)", len(x.Args)),
		}
	}
	sb.WriteString("count()")
	return nil
}

func writeCountIfFunction(ctx *exprContext, sb *strings.Builder, x *parser.CallExpr) error {
	if len(x.Args) != 1 {
		return &compileError{
			source: ctx.source,
			span: parser.Span{
				Start: x.Lparen.End,
				End:   x.Rparen.Start,
			},
			err: fmt.Errorf("countif(x) takes a single argument (got %d)", len(x.Args)),
		}
	}
	sb.WriteString("count() FILTER (WHERE ")
	if err := writeExpression(ctx, sb, x.Args[0], x); err != nil {
		return err
	}
	sb.WriteString(")")
	return nil
}

func writeIfFunction(ctx *exprContext, sb *strings.Builder, x *parser.CallExpr) error {
	if len(x.Args) != 3 {
		return &compileError{
			source: ctx.source,
			span: parser.Span{
				Start: x.Lparen.End,
				End:   x.Rparen.Start,
			},
			err: fmt.Errorf("%s(if, then, else) takes 3 arguments (got %d)", x.Func.Name, len(x.Args)),
		}
	}
	sb.WriteString("CASE WHEN coalesce(")
	if err := writeExpression(ctx, sb, x.Args[0], x); err != nil {
		return err
	}
	sb.WriteString(", FALSE) THEN ")
	if err := writeExpression(ctx, sb, x.Args[1], x); err != nil {
		return err
	}
	sb.WriteString(" ELSE ")
	if err := writeExpression(ctx, sb, x.Args[2], x); err != nil {
		return err
	}
	sb.WriteString(" END")
	return nil
}

func writeToLowerFunction(ctx *exprContext, sb *strings.Builder, x *parser.CallExpr) error {
	if len(x.Args) != 1 {
		return &compileError{
			source: ctx.source,
			span: parser.Span{
				Start: x.Lparen.End,
				End:   x.Rparen.Start,
			},
			err: fmt.Errorf("tolower(x) takes a single argument (got %d)", len(x.Args)),
		}
	}
	sb.WriteString("LOWER(")
	if err := writeExpression(ctx, sb, x.Args[0], x); err != nil {
		return err
	}
	sb.WriteString(")")
	return nil
}

func writeToUpperFunction(ctx *exprContext, sb *strings.Builder, x *parser.CallExpr) error {
	if len(x.Args) != 1 {
		return &compileError{
			source: ctx.source,
			span: parser.Span{
				Start: x.Lparen.End,
				End:   x.Rparen.Start,
			},
			err: fmt.Errorf("toupper(x) takes a single argument (got %d)", len(x.Args)),
		}
	}
	sb.WriteString("UPPER(")
	if err := writeExpression(ctx, sb, x.Args[0], x); err != nil {
		return err
	}
	sb.WriteString(")")
	return nil
}

func quoteSQLString(sb *strings.Builder, s string) {
	sb.WriteString("'")
	for _, b := range []byte(s) {
		if b == '\'' {
			sb.WriteString("''")
		} else {
			sb.WriteByte(b)
		}
	}
	sb.WriteString("'")
}

type compileError struct {
	source string
	span   parser.Span
	err    error
}

func (e *compileError) Error() string {
	if !e.span.IsValid() {
		return e.err.Error()
	}
	line, col := linecol(e.source, e.span.Start)
	return fmt.Sprintf("%d:%d: %s", line, col, e.err.Error())
}

func (e *compileError) Unwrap() error {
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
