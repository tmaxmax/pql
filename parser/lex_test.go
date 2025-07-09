// Copyright 2024 RunReveal Inc.
// SPDX-License-Identifier: Apache-2.0

package parser

import (
	"testing"

	"github.com/google/go-cmp/cmp"
	"github.com/google/go-cmp/cmp/cmpopts"
)

var lexTests = []struct {
	name  string
	query string
	want  []Token
}{
	{
		name:  "Empty",
		query: "",
		want:  []Token{},
	},
	{
		name:  "SingleIdent",
		query: "StormEvents\n",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 11), Value: "StormEvents"},
		},
	},
	{
		name:  "Pipeline",
		query: "foo | bar",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 3), Value: "foo"},
			{Kind: TokenPipe, Span: newSpan(4, 5)},
			{Kind: TokenIdentifier, Span: newSpan(6, 9), Value: "bar"},
		},
	},
	{
		name:  "QuotedIdent",
		query: "`foo`\n",
		want: []Token{
			{Kind: TokenQuotedIdentifier, Span: newSpan(0, 5), Value: "foo"},
		},
	},
	{
		name:  "QuotedIdentDoubled",
		query: "`x``y`\n",
		want: []Token{
			{Kind: TokenQuotedIdentifier, Span: newSpan(0, 6), Value: "x`y"},
		},
	},
	{
		name:  "UnterminatedQuotedIdent",
		query: "`foo",
		want: []Token{
			{Kind: TokenError, Span: newSpan(0, 4)},
		},
	},
	{
		name:  "LineSplitQuotedIdent",
		query: "`foo\nbar`",
		want: []Token{
			{Kind: TokenError, Span: newSpan(0, 4)},
			{Kind: TokenIdentifier, Span: newSpan(5, 8), Value: "bar"},
			{Kind: TokenError, Span: newSpan(8, 9)},
		},
	},
	{
		name:  "SingleQuotedMapKey",
		query: "['foo']\n",
		want: []Token{
			{Kind: TokenLBracket, Span: newSpan(0, 1)},
			{Kind: TokenString, Span: newSpan(1, 6), Value: "foo"},
			{Kind: TokenRBracket, Span: newSpan(6, 7)},
		},
	},
	{
		name:  "DoubleQuotedMapKey",
		query: `["foo"]`,
		want: []Token{
			{Kind: TokenLBracket, Span: newSpan(0, 1)},
			{Kind: TokenString, Span: newSpan(1, 6), Value: "foo"},
			{Kind: TokenRBracket, Span: newSpan(6, 7)},
		},
	},
	{
		name:  "UnterminatedMapKey",
		query: `["foo"`,
		want: []Token{
			{Kind: TokenLBracket, Span: newSpan(0, 1)},
			{Kind: TokenString, Span: newSpan(1, 6), Value: "foo"},
		},
	},
	{
		name:  "LineSplitMapKey",
		query: "['foo\nbar']",
		want: []Token{
			{Kind: TokenLBracket, Span: newSpan(0, 1)},
			{Kind: TokenError, Span: newSpan(1, 5)},
			{Kind: TokenIdentifier, Span: newSpan(6, 9), Value: "bar"},
			{Kind: TokenError, Span: newSpan(9, 11)},
		},
	},
	{
		name:  "Comments",
		query: "StormEvents // the table name\n// Another comment\n| count",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 11), Value: "StormEvents"},
			{Kind: TokenPipe, Span: newSpan(49, 50)},
			{Kind: TokenIdentifier, Span: newSpan(51, 56), Value: "count"},
		},
	},
	{
		name:  "Slash",
		query: "foo / bar",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 3), Value: "foo"},
			{Kind: TokenSlash, Span: newSpan(4, 5)},
			{Kind: TokenIdentifier, Span: newSpan(6, 9), Value: "bar"},
		},
	},
	{
		name:  "SlashAtEOF",
		query: "foo /",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 3), Value: "foo"},
			{Kind: TokenSlash, Span: newSpan(4, 5)},
		},
	},
	{
		name:  "Zero",
		query: "0",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 1), Value: "0"},
		},
	},
	{
		name:  "LeadingZeroes",
		query: "007",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 3), Value: "7"},
		},
	},
	{
		name:  "Integer",
		query: "123",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 3), Value: "123"},
		},
	},
	{
		name:  "Float",
		query: "3.14",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 4), Value: "3.14"},
		},
	},
	{
		name:  "Exponent",
		query: "1e-9",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 4), Value: "1e-9"},
		},
	},
	{
		name:  "ZeroExponent",
		query: "0e9",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 3), Value: "0e9"},
		},
	},
	{
		name:  "LeadingDot",
		query: ".001",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 4), Value: "0.001"},
		},
	},
	{
		name:  "ZeroDotDecimal",
		query: "0.001",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 5), Value: "0.001"},
		},
	},
	{
		name:  "LeadingDotIdentifier",
		query: ".foo",
		want: []Token{
			{Kind: TokenDot, Span: newSpan(0, 1)},
			{Kind: TokenIdentifier, Span: newSpan(1, 4), Value: "foo"},
		},
	},
	{
		name:  "Hexadecimal",
		query: "0xdeadbeef",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 10), Value: "3735928559"},
		},
	},
	{
		name:  "UnterminatedHex",
		query: "0x",
		want: []Token{
			{Kind: TokenError, Span: newSpan(0, 2)},
		},
	},
	{
		name:  "BrokenHex",
		query: "0xy",
		want: []Token{
			{Kind: TokenError, Span: newSpan(0, 2)},
			{Kind: TokenIdentifier, Span: newSpan(2, 3), Value: "y"},
		},
	},
	{
		name:  "JustDot",
		query: ".",
		want: []Token{
			{Kind: TokenDot, Span: newSpan(0, 1)},
		},
	},
	{
		name:  "SingleQuotedLiteral",
		query: `'abc'`,
		want: []Token{
			{Kind: TokenString, Span: newSpan(0, 5), Value: "abc"},
		},
	},
	{
		name:  "DoubleQuotedLiteral",
		query: `"abc"`,
		want: []Token{
			{Kind: TokenString, Span: newSpan(0, 5), Value: "abc"},
		},
	},
	{
		name:  "UnterminatedString",
		query: `"abc`,
		want: []Token{
			{Kind: TokenError, Span: newSpan(0, 4)},
		},
	},
	{
		name:  "StringWithNewline",
		query: "\"abc\ndef\"",
		want: []Token{
			{Kind: TokenError, Span: newSpan(0, 4)},
			{Kind: TokenIdentifier, Span: newSpan(5, 8), Value: "def"},
			{Kind: TokenError, Span: newSpan(8, 9)},
		},
	},
	{
		name:  "StringWithEscapes",
		query: `"abc\"\n\t\\def"`,
		want: []Token{
			{Kind: TokenString, Span: newSpan(0, 16), Value: "abc\"\n\t\\def"},
		},
	},
	{
		name:  "StringWithEOFAfterBackslash",
		query: `"abc\`,
		want: []Token{
			{Kind: TokenError, Span: newSpan(0, 5)},
		},
	},
	{
		name:  "StringWithNewlineAfterBackslash",
		query: `"abc\` + "\n" + `def"`,
		want: []Token{
			{Kind: TokenError, Span: newSpan(0, 5)},
			{Kind: TokenIdentifier, Span: newSpan(6, 9), Value: "def"},
			{Kind: TokenError, Span: newSpan(9, 10)},
		},
	},
	{
		name:  "Parentheses",
		query: "(x)",
		want: []Token{
			{Kind: TokenLParen, Span: newSpan(0, 1)},
			{Kind: TokenIdentifier, Span: newSpan(1, 2), Value: "x"},
			{Kind: TokenRParen, Span: newSpan(2, 3)},
		},
	},
	{
		name:  "And",
		query: "this and that",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 4), Value: "this"},
			{Kind: TokenAnd, Span: newSpan(5, 8)},
			{Kind: TokenIdentifier, Span: newSpan(9, 13), Value: "that"},
		},
	},
	{
		name:  "Or",
		query: "this or that",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 4), Value: "this"},
			{Kind: TokenOr, Span: newSpan(5, 7)},
			{Kind: TokenIdentifier, Span: newSpan(8, 12), Value: "that"},
		},
	},
	{
		name:  "Equals",
		query: "x == 5",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 1), Value: "x"},
			{Kind: TokenEq, Span: newSpan(2, 4)},
			{Kind: TokenNumber, Span: newSpan(5, 6), Value: "5"},
		},
	},
	{
		name:  "NotEquals",
		query: "x != 5",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 1), Value: "x"},
			{Kind: TokenNE, Span: newSpan(2, 4)},
			{Kind: TokenNumber, Span: newSpan(5, 6), Value: "5"},
		},
	},
	{
		name:  "WhereClause",
		query: `where EventType == "Tornado" or EventType != "Thunderstorm Wind"`,
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 5), Value: "where"},
			{Kind: TokenIdentifier, Span: newSpan(6, 15), Value: "EventType"},
			{Kind: TokenEq, Span: newSpan(16, 18)},
			{Kind: TokenString, Span: newSpan(19, 28), Value: "Tornado"},
			{Kind: TokenOr, Span: newSpan(29, 31)},
			{Kind: TokenIdentifier, Span: newSpan(32, 41), Value: "EventType"},
			{Kind: TokenNE, Span: newSpan(42, 44)},
			{Kind: TokenString, Span: newSpan(45, 64), Value: "Thunderstorm Wind"},
		},
	},
	{
		name:  "Add",
		query: "3.14 + 3.14",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 4), Value: "3.14"},
			{Kind: TokenPlus, Span: newSpan(5, 6)},
			{Kind: TokenNumber, Span: newSpan(7, 11), Value: "3.14"},
		},
	},
	{
		name:  "Subtract",
		query: "0.23 - 0.22",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 4), Value: "0.23"},
			{Kind: TokenMinus, Span: newSpan(5, 6)},
			{Kind: TokenNumber, Span: newSpan(7, 11), Value: "0.22"},
		},
	},
	{
		name:  "Multiply",
		query: "2 * 2",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 1), Value: "2"},
			{Kind: TokenStar, Span: newSpan(2, 3)},
			{Kind: TokenNumber, Span: newSpan(4, 5), Value: "2"},
		},
	},
	{
		name:  "Divide",
		query: "4 / 2",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 1), Value: "4"},
			{Kind: TokenSlash, Span: newSpan(2, 3)},
			{Kind: TokenNumber, Span: newSpan(4, 5), Value: "2"},
		},
	},
	{
		name:  "Modulo",
		query: "4 % 2",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 1), Value: "4"},
			{Kind: TokenMod, Span: newSpan(2, 3)},
			{Kind: TokenNumber, Span: newSpan(4, 5), Value: "2"},
		},
	},
	{
		name:  "Less",
		query: "1 < 10",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 1), Value: "1"},
			{Kind: TokenLT, Span: newSpan(2, 3)},
			{Kind: TokenNumber, Span: newSpan(4, 6), Value: "10"},
		},
	},
	{
		name:  "Greater",
		query: "0.23 > 0.22",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 4), Value: "0.23"},
			{Kind: TokenGT, Span: newSpan(5, 6)},
			{Kind: TokenNumber, Span: newSpan(7, 11), Value: "0.22"},
		},
	},
	{
		name:  "LessOrEqual",
		query: "4 <= 5",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 1), Value: "4"},
			{Kind: TokenLE, Span: newSpan(2, 4)},
			{Kind: TokenNumber, Span: newSpan(5, 6), Value: "5"},
		},
	},
	{
		name:  "GreaterOrEqual",
		query: "5 >= 4",
		want: []Token{
			{Kind: TokenNumber, Span: newSpan(0, 1), Value: "5"},
			{Kind: TokenGE, Span: newSpan(2, 4)},
			{Kind: TokenNumber, Span: newSpan(5, 6), Value: "4"},
		},
	},
	{
		name:  "CaseInsensitiveEquals",
		query: `"abc" =~ "ABC"`,
		want: []Token{
			{Kind: TokenString, Span: newSpan(0, 5), Value: "abc"},
			{Kind: TokenCaseInsensitiveEq, Span: newSpan(6, 8)},
			{Kind: TokenString, Span: newSpan(9, 14), Value: "ABC"},
		},
	},
	{
		name:  "CaseInsensitiveNotEquals",
		query: `"aBc" !~ "xyz"`,
		want: []Token{
			{Kind: TokenString, Span: newSpan(0, 5), Value: "aBc"},
			{Kind: TokenCaseInsensitiveNE, Span: newSpan(6, 8)},
			{Kind: TokenString, Span: newSpan(9, 14), Value: "xyz"},
		},
	},
	{
		name:  "ExpressionList",
		query: "a, b, c",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 1), Value: "a"},
			{Kind: TokenComma, Span: newSpan(1, 2)},
			{Kind: TokenIdentifier, Span: newSpan(3, 4), Value: "b"},
			{Kind: TokenComma, Span: newSpan(4, 5)},
			{Kind: TokenIdentifier, Span: newSpan(6, 7), Value: "c"},
		},
	},
	{
		name:  "WhereFilter",
		query: "StormEvents | where true",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 11), Value: "StormEvents"},
			{Kind: TokenPipe, Span: newSpan(12, 13)},
			{Kind: TokenIdentifier, Span: newSpan(14, 19), Value: "where"},
			{Kind: TokenIdentifier, Span: newSpan(20, 24), Value: "true"},
		},
	},
	{
		name:  "Fuzz8adaab75de5f9003",
		query: "vents | \x00\x10\x00\x00M=",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 5), Value: "vents"},
			{Kind: TokenPipe, Span: newSpan(6, 7)},
			{Kind: TokenError, Span: newSpan(8, 9)},
			{Kind: TokenError, Span: newSpan(9, 10)},
			{Kind: TokenError, Span: newSpan(10, 11)},
			{Kind: TokenError, Span: newSpan(11, 12)},
			{Kind: TokenIdentifier, Span: newSpan(12, 13), Value: "M"},
			{Kind: TokenAssign, Span: newSpan(13, 14)},
		},
	},
	{
		name:  "DottedIdentifier",
		query: "Table.Column",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 5), Value: "Table"},
			{Kind: TokenDot, Span: newSpan(5, 6)},
			{Kind: TokenIdentifier, Span: newSpan(6, 12), Value: "Column"},
		},
	},
	{
		name:  "DollarIdentifier",
		query: "$left.Column",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 5), Value: "$left"},
			{Kind: TokenDot, Span: newSpan(5, 6)},
			{Kind: TokenIdentifier, Span: newSpan(6, 12), Value: "Column"},
		},
	},
	{
		name:  "DollarInIdentifier",
		query: "x$y",
		want: []Token{
			{Kind: TokenIdentifier, Span: newSpan(0, 1), Value: "x"},
			{Kind: TokenIdentifier, Span: newSpan(1, 3), Value: "$y"},
		},
	},
	{
		name:  "Macro",
		query: "#x(y,'z')",
		want: []Token{
			{Kind: TokenHash, Span: newSpan(0, 1)},
			{Kind: TokenIdentifier, Span: newSpan(1, 2), Value: "x"},
			{Kind: TokenLParen, Span: newSpan(2, 3)},
			{Kind: TokenIdentifier, Span: newSpan(3, 4), Value: "y"},
			{Kind: TokenComma, Span: newSpan(4, 5)},
			{Kind: TokenString, Span: newSpan(5, 8), Value: "z"},
			{Kind: TokenRParen, Span: newSpan(8, 9)},
		},
	},
}

func TestScan(t *testing.T) {
	equateErrorTokens := cmp.FilterValues(func(tok1, tok2 Token) bool {
		return tok1.Kind == TokenError && tok2.Kind == TokenError
	}, cmp.Comparer(func(tok1, tok2 Token) bool {
		tok1.Value = ""
		tok2.Value = ""
		return tok1 == tok2
	}))

	for _, test := range lexTests {
		t.Run(test.name, func(t *testing.T) {
			got := Scan(test.query)

			if diff := cmp.Diff(test.want, got, cmpopts.EquateEmpty(), equateErrorTokens); diff != "" {
				t.Errorf("Scan(%q) (-want +got):\n%s", test.query, diff)
			}
		})
	}
}

func FuzzScan(f *testing.F) {
	for _, test := range lexTests {
		f.Add(test.query)
	}

	f.Fuzz(func(t *testing.T, query string) {
		got := Scan(query)
		for i, tok := range got {
			if !tok.Span.IsValid() {
				t.Errorf("Scan(%q)[%d].Span is invalid", query, i)
				continue
			}
			if tok.Span.Start > len(query) || tok.Span.End > len(query) {
				t.Errorf("Scan(%q)[%d].Span = %v; out of bounds of [0,%d)", query, i, tok.Span, len(query))
			}
		}
	})
}

func BenchmarkScan(b *testing.B) {
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		Scan(`StormEvents | where EventType == "Tornado" or EventType != "Thunderstorm Wind"`)
	}
}

func TestSplitStatements(t *testing.T) {
	tests := []struct {
		source string
		want   []string
	}{
		{"", []string{""}},
		{"foo", []string{"foo"}},
		{"foo;bar", []string{"foo", "bar"}},
		{"foo';'bar", []string{"foo';'bar"}},
	}
	for _, test := range tests {
		got := SplitStatements(test.source)
		if diff := cmp.Diff(test.want, got); diff != "" {
			t.Errorf("SplitStatements(%q) (-want +got):\n%s", test.source, diff)
		}
	}
}
