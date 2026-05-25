package util

// Helpers used by the rule under test.
// Go port of example.RuleReturnConditional. The Java rule's method-signature
// pattern with `pattern-inside` cannot be expressed in the Go pipeline
// (MethodEnter/MethodExit edges are dropped). The Go port preserves the
// fixture's *spirit*: a helper that conditionally returns the source-derived
// value or a safe alternative.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

// Positive: helper returns source via the if branch.
func Positive_returns_source_or_derived() {
	Sink(conditionalHelper(Source()))
}

func conditionalHelper(src string) string {
	var ret string
	if src != "" {
		ret = src
	} else {
		ret = "fallback"
	}
	return ret
}

// Negative: helper always returns a fresh safe value, regardless of source.
func Negative_always_safe() {
	Sink(alwaysSafeHelper(Source()))
}

func alwaysSafeHelper(src string) string {
	_ = src
	var safe string
	if true {
		safe = "safe"
	}
	return safe
}
