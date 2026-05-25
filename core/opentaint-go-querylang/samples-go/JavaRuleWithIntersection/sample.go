package util

// Helpers used by the rule under test.
// Go port of example.RuleWithIntersection. The Java rule combines two
// equivalent `$X = src(); ...; sink($X)` patterns under `patterns:`,
// requiring both to match (intersection). In Go's taint mode the
// natural equivalent is the single source-to-sink rule with two
// distinct positive runs.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

// Positive_simple: direct flow from Source to Sink.
func Positive_simple() {
	data := Source()
	Sink(data)
}

// Negative_no_sink: source assigned but never reaches sink.
func Negative_no_sink() {
	data := Source()
	_ = data
}

// Negative_no_source: sink called with constant — no taint.
func Negative_no_source() {
	Sink("random data")
}
