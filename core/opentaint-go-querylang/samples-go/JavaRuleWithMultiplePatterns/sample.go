package util

// Helpers used by the rule under test.
// Go port of example.RuleWithMultiplePatterns. The Java rule chains three
// patterns (`SOURCE.mkType2()` → `mkType3()` → `mkType1()`) all of which
// must intersect inside one function. In Go the closest available
// construct is three distinct source patterns under `pattern-sources`,
// any one of which reaching Sink fires the rule.
func SourceA() string { return "ta" }
func SourceB() string { return "tb" }
func SourceC() string { return "tc" }
func Sink(s string)   { _ = s }

// Positive_a: taint from SourceA reaches sink.
func Positive_a() {
	Sink(SourceA())
}

// Positive_b: taint from SourceB reaches sink.
func Positive_b() {
	Sink(SourceB())
}

// Positive_c: taint from SourceC reaches sink.
func Positive_c() {
	Sink(SourceC())
}

// Negative_no_source: Sink called with a constant.
func Negative_no_source() {
	Sink("safe")
}
