package util

// Helpers used by the rule under test.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

// Positive_basic: directly pipes tainted output of Source into Sink.
func Positive_basic() {
	Sink(Source())
}

// Negative_unrelated: Sink is called, but with a constant — no taint flows.
func Negative_unrelated() {
	Sink("constant")
}
