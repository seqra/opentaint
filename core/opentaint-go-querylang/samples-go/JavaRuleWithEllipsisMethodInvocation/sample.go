package util

// Helpers used by the rule under test.
// Go port of example.RuleWithEllipsisMethodInvocation, recast to use the
// closest idiomatic Go construct: ellipsis trailing arguments at the sink
// (the Java rule's `$A. ... .toString()` is Java-only method-chain ellipsis).
func Source() string                       { return "tainted" }
func Sink(first string, rest ...string)    { _ = first; _ = rest }

// Positive_zero_extra: sink called with one arg — matches `Sink($X, ...)` with empty tail.
func Positive_zero_extra() {
	data := Source()
	Sink(data)
}

// Positive_with_extra: sink called with extra trailing args — matches with non-empty tail.
func Positive_with_extra() {
	data := Source()
	Sink(data, "log", "ctx")
}

// Negative_no_source: sink called but the first arg is a constant, not from Source.
func Negative_no_source() {
	Sink("constant", "log")
}
