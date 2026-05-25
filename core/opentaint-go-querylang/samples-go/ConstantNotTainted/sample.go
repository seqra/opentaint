package util

// Helpers used by the rule under test.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

// Positive_tainted: tainted value reaches Sink — argument is not the "safe" literal.
func Positive_tainted() {
	Sink(Source())
}

// Negative_safe_literal: Sink called with the exact literal "safe" — excluded by pattern-not.
func Negative_safe_literal() {
	Sink("safe")
}
