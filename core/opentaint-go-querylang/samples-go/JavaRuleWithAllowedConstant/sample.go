package util

// Helpers used by the rule under test.
// Go port of example.RuleWithAllowedConstant. The Java rule matches any
// `sink(...)` except `sink("...")` (string-constant arg is allowed). In
// Go this is `pattern-not: util.Sink("...")` — i.e. constant-string sinks
// are exempt.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

// Positive_simple: tainted (non-constant) reaches Sink.
func Positive_simple() {
	data := Source()
	Sink(data)
}

// Positive_with_ellipsis: tainted (non-constant) with intervening noop.
func Positive_with_ellipsis() {
	data := Source()
	_ = data + "x"
	Sink(data)
}

// Positive_iter_proc: tainted (non-constant) flows through a wrapper.
func Positive_iter_proc() {
	data := Source()
	sinkWrapper(data)
}

func sinkWrapper(data string) {
	Sink(data)
}

// Negative_simple: Sink called with a string constant — exempted by pattern-not.
func Negative_simple() {
	Sink("Constant")
}
