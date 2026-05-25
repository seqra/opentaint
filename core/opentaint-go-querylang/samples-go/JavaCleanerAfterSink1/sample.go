package util

// Helpers used by the rule under test.
// Go port of example.CleanerAfterSink1. The Java rule uses
// `pattern-not-inside: $A = src(); ...; sink($A); ...; clean($A);` —
// i.e. suppress only if a clean follows the sink. In Go's forward
// dataflow a cleaner that runs after the sink does NOT retroactively
// drop the sink fact; so positives here are positives that the Java
// rule would have suppressed but Go correctly reports.
func Source() string         { return "tainted" }
func Sink(s string)          { _ = s }
func Clean(s string) string  { return s }

// Positive_simple: bare source-to-sink, no clean at all.
func Positive_simple() {
	o := Source()
	Sink(o)
}

// Positive_clean_after_sink: clean follows the sink — Go's forward dataflow
// cannot retroactively suppress; the sink fact has already been reported.
// (Java with `pattern-not-inside` would have suppressed this.)
func Positive_clean_after_sink() {
	o := Source()
	Sink(o)
	_ = Clean(o)
}

// Negative_clean_before_sink: clean precedes sink — taint is dropped.
func Negative_clean_before_sink() {
	o := Source()
	cleaned := Clean(o)
	Sink(cleaned)
}

// Positive_multiple_functions: taint flows through nested helper functions
// without any sanitizer along the way.
func Positive_multiple_functions() {
	o := nestedSrc()
	nestedSink(o)
}

func nestedSrc() string { return Source() }
func nestedSink(o string) {
	Sink(o)
}
