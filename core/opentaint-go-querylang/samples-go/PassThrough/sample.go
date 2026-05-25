package util

// Helpers used by the rule under test.
func Source() string         { return "tainted" }
func Sink(s string)          { _ = s }
func Wrap(s string) string   { return s }

// Positive_via_wrap: Wrap propagates taint from arg to return.
func Positive_via_wrap() {
	Sink(Wrap(Source()))
}

// Negative_no_wrap: nothing flows through Wrap; the sink receives a constant.
func Negative_no_wrap() {
	Sink("foo")
}
