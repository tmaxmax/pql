package parser

import (
	"errors"
	"fmt"
	"io"
	"reflect"
	"slices"
	"strings"
)

func ParseNode(offset int, node string) (Node, error) {
	tokens := Scan(node)
	p := func() *parser {
		return &parser{
			source: node,
			tokens: tokens,
		}
	}

	n, err := firstParse(
		parseNode(p().letStatement),
		parseNode(func() (*TabularExpr, error) {
			t := p()
			t.split(TokenPipe)
			if _, ok := t.next(); !ok {
				return nil, notFoundError{io.EOF}
			}

			return p().tabularExpr()
		}),
		parseNode(p().macro),
		parseOperatorNode(p(), (*parser).countOperator, "count"),
		parseOperatorNode(p(), (*parser).whereOperator, "where", "filter"),
		parseOperatorNode(p(), (*parser).sortOperator, "sort", "order"),
		parseOperatorNode(p(), (*parser).takeOperator, "take", "limit"),
		parseOperatorNode(p(), (*parser).topOperator, "top"),
		parseOperatorNode(p(), (*parser).projectOperator, "project"),
		parseOperatorNode(p(), (*parser).extendOperator, "extend"),
		parseOperatorNode(p(), (*parser).summarizeOperator, "summarize"),
		parseOperatorNode(p(), (*parser).asOperator, "as"),
		parseOperatorNode(p(), (*parser).renderOperator, "render"),
		// TODO: add other nodes
		func() (Node, error) {
			return p().expr()
		},
	)
	if err != nil {
		var perr *parseError
		if errors.As(err, &perr) {
			perr.span.Start += offset
			perr.span.End += offset
		}

		return nil, err
	}

	if offset != 0 {
		spanT := reflect.TypeOf(Span{})

		Walk(n, func(n Node) bool {
			v := reflect.Indirect(reflect.ValueOf(n))
			for i := 0; i < v.NumField(); i++ {
				f := v.Field(i)
				if f.Type().AssignableTo(spanT) {
					s := f.Addr().Interface().(*Span)
					if *s != nullSpan() {
						s.Start += offset
						s.End += offset
					}
				}
			}

			return true
		})
	}

	return n, nil
}

type nodeParser[T any] interface {
	*T
	Node
}

func parseNode[T any, P nodeParser[T]](p func() (P, error)) func() (Node, error) {
	return func() (Node, error) {
		v, err := p()
		if v == nil {
			return nil, err
		}
		return v, err
	}
}

type tabularOperatorParser[T any] interface {
	*T
	TabularOperator
}

func parseOperatorNode[T any, P tabularOperatorParser[T]](p *parser, pf func(*parser, Token, Token) (P, error), keywords ...string) func() (Node, error) {
	return parseNode(func() (P, error) {
		tok, _ := p.next()
		if tok.Kind != TokenIdentifier || !slices.Contains(keywords, tok.Value) {
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

		return pf(p, pipe, tok)
	})
}
