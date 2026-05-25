package util

// Helpers used by the rule under test.
// Go port of example.RuleWithPatternInside. The Java rule combines
// `pattern-inside: $A = src(); ...` with `pattern: sink($A)`; in the Go
// taint pipeline the equivalent is source/sink with `pattern-inside`
// scoping subsumed into source rule.
func Source() string  { return "tainted" }
func Source1() string { return "untainted" }
func Sink(s string)   { _ = s }

// Positive_simple: direct source-to-sink flow.
func Positive_simple() {
	data := Source()
	Sink(data)
}

// Positive_with_ellipsis: intervening stmt between source assignment and sink.
func Positive_with_ellipsis() {
	data := Source()
	_ = data + "x"
	Sink(data)
}

// Positive_iter_proc: taint reaches Sink through an interprocedural wrapper.
func Positive_iter_proc() {
	data := Source()
	sinkWrapper(data)
}

func sinkWrapper(data string) {
	_ = data + "x"
	Sink(data)
}

// Negative_no_sink: source assigned but never reaches sink.
func Negative_no_sink() {
	data := Source()
	_ = data
}

// Negative_no_source: Sink called with a value from a non-source helper.
func Negative_no_source() {
	data := Source1()
	Sink(data)
}
