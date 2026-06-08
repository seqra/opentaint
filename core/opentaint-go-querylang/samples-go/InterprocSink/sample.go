package util

// Helpers used by the rule under test.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

// Wrapper just forwards to Sink — taint must follow across the call.
func wrapper(x string) {
	Sink(x)
}

// Positive_via_wrapper: tainted value crosses one call boundary to reach Sink.
func Positive_via_wrapper() {
	wrapper(Source())
}

// Negative_direct_constant: wrapper called with a constant, no taint reaches Sink.
func Negative_direct_constant() {
	wrapper("constant")
}
