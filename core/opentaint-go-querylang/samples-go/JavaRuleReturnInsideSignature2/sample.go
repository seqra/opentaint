package util

// Go port of example.RuleReturnInsideSignature2. Java rule wraps a
// src->pass->return chain in a signature constraint and a second pattern-inside
// `$F = pass($ARG); ...`. Recast in Go as Pass source → Sink call.
func Pass(s string) string { return s }
func Sink(s string)        { _ = s }

func Positive_simple() {
	a := Pass("data")
	Sink(a)
}

func Negative_no_pass() {
	Sink("safe")
}
