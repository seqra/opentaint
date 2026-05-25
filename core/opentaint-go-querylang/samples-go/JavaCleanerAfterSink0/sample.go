package util

// Go port of example.CleanerAfterSink0. Java rule: `$A = src(); ...; sink($A);`
// with `pattern-not-inside: ...; sink($A); ...; clean();` (clean after sink
// suppresses the match in Java's AST view). In Go's forward dataflow, a
// cleaner that runs after the sink does not retroactively drop the taint
// reported at the sink — these are Java false-negatives that Go correctly
// catches.
func Source() string         { return "tainted" }
func Clean(s string) string  { return s }
func Sink(s string)          { _ = s }

// Positive_simple: bare source -> sink, no cleaner.
func Positive_simple() {
	o := Source()
	Sink(o)
}

// Positive_clean_after_sink: cleaner runs after the sink — Go reports anyway.
func Positive_clean_after_sink() {
	o := Source()
	Sink(o)
	_ = Clean(o)
}

// Negative_clean_before_sink: clean BEFORE sink, taint is dropped.
func Negative_clean_before_sink() {
	o := Source()
	cleaned := Clean(o)
	Sink(cleaned)
}
