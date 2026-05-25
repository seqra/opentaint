package util

// Go port of example.CleanerAfterSink2. Two-arg sink/clean form. Same forward-
// dataflow caveat as JavaCleanerAfterSink0/1: cleaners after the sink don't
// retroactively drop the report.
func Source() string                  { return "tainted" }
func Copy(s string) string            { return s }
func Sink(a string, b string)         { _, _ = a, b }
func Clean(a string, b string) string { return a + b }

// Positive_simple: source -> copy -> two-arg sink.
func Positive_simple() {
	a := Source()
	b := Copy(a)
	Sink(a, b)
}

// Positive_clean_after_sink: cleaner after the sink doesn't suppress.
func Positive_clean_after_sink() {
	a := Source()
	b := Copy(a)
	Sink(a, b)
	_ = Clean(a, b)
}

// Negative_clean_before_sink: cleaner before sink drops the taint.
func Negative_clean_before_sink() {
	a := Source()
	b := Copy(a)
	cleaned := Clean(a, b)
	_ = cleaned
}
