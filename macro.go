package pql

import (
	"fmt"

	"github.com/runreveal/pql/parser"
)

func macroFromDefine(d *parser.Define) Macro {
	return func(macro *parser.Macro, parent parser.Node) (parser.Node, error) {
		if len(macro.Args) != len(d.Args) {
			return nil, fmt.Errorf("expected %d args, got %d", len(macro.Args), len(d.Args))
		}

		n, err := d.Body()
		if err != nil {
			return nil, fmt.Errorf("parse macro: %w", err)
		}

		sub := macroSubstitutor{
			args:   map[string]parser.Expr{},
			parent: parent,
		}
		for i, marg := range macro.Args {
			sub.args[d.Args[i].Name] = marg
		}

		parser.Walk(n, func(n parser.Node) bool {
			switch n := n.(type) {
			case *parser.TableRef:
				sub.ident(&n.Table)
			case *parser.AsOperator:
				sub.ident(&n.Name)
			case *parser.WhereOperator:
				return sub.expr(&n.Predicate)
			case *parser.SortTerm:
				return sub.expr(&n.X)
			case *parser.TakeOperator:
				return sub.expr(&n.RowCount)
			case *parser.TopOperator:
				return sub.expr(&n.RowCount)
			case *parser.ProjectColumn:
				sub.ident(&n.Name)
				return sub.expr(&n.X)
			case *parser.ExtendColumn:
				sub.ident(&n.Name)
				return sub.expr(&n.X)
			case *parser.SummarizeColumn:
				sub.ident(&n.Name)
				return sub.expr(&n.X)
			case *parser.JoinOperator:
				sub.ident(&n.Flavor)
				sub.exprList(n.Conditions)
				// recurse on table.
				return sub.further()
			case *parser.BinaryExpr:
				return sub.expr(&n.X) || sub.expr(&n.Y)
			case *parser.UnaryExpr:
				return sub.expr(&n.X)
			case *parser.InExpr:
				return sub.expr(&n.X) || sub.exprList(n.Vals)
			case *parser.ParenExpr:
				return sub.expr(&n.X)
			case *parser.CallExpr:
				sub.ident(&n.Func)
				return sub.exprList(n.Args)
			case *parser.Macro:
				return sub.exprList(n.Args)
			case *parser.IndexExpr:
				return sub.expr(&n.X) || sub.expr(&n.Index)
			case *parser.RenderOperator:
				sub.ident(&n.ChartType)
				// recurse on props.
				return sub.further()
			case *parser.RenderProperty:
				sub.ident(&n.Name)
				return sub.expr(&n.Value)
			case *parser.Define, *parser.LetStatement:
				// shouldn't happen.
				return false
			default:
				return sub.further()
			}

			return false
		})

		return n, err
	}
}

type macroSubstitutor struct {
	args   map[string]parser.Expr
	parent parser.Node
	err    error
}

func (m *macroSubstitutor) ident(id **parser.Ident) {
	if m.err != nil {
		return
	}

	arg, ok := m.args[(*id).Name]
	if !ok {
		return
	}

	q, ok := arg.(*parser.QualifiedIdent)
	if !ok || len(q.Parts) != 1 {
		m.err = fmt.Errorf("invalid parameter for identifier %q", (*id).Name)
		return
	}

	*id = q.Parts[0]
}

func (m *macroSubstitutor) expr(ex *parser.Expr) bool {
	if m.err != nil {
		return false
	}

	q, ok := (*ex).(*parser.QualifiedIdent)
	if !ok {
		return true
	}

	switch {
	case len(q.Parts) == 1:
		arg, ok := m.args[q.Parts[0].Name]
		if ok {
			*ex = arg
		}
	case len(q.Parts) == 2:
		switch q.Parts[0].Name {
		case "$left", "$right":
			name := q.Parts[1].Name
			arg, ok := m.args[name]
			if ok {
				qarg, ok := arg.(*parser.QualifiedIdent)
				if ok && len(qarg.Parts) == 1 {
					q.Parts[1] = qarg.Parts[0]
				}
			}
		}
	}

	return false
}

func (m *macroSubstitutor) exprList(exs []parser.Expr) bool {
	further := false
	for i := range exs {
		further = further || m.expr(&exs[i])
	}
	return further
}

func (m *macroSubstitutor) further() bool {
	return m.err == nil
}
