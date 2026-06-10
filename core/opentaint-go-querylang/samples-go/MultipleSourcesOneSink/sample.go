package util

// Helpers used by the rule under test.
func Source() string { return "tainted-a" }
func Other() string  { return "tainted-b" }
func Sink(s string)  { _ = s }

// Positive_source_a: taint originates from util.Source.
func Positive_source_a() {
	Sink(Source())
}

// Positive_source_b: taint originates from util.Other.
func Positive_source_b() {
	Sink(Other())
}

// Negative_no_source: Sink called with a constant — neither source touches it.
func Negative_no_source() {
	Sink("clean")
}
