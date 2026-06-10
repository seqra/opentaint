package util

// Helpers used by the rule under test (mirrors example.Rule's src/clean/sink).
func Source() string        { return "tainted" }
func Clean(s string) string { return s }
func Sink(s string)         { _ = s }

// PositiveSimple: direct flow from Source to Sink.
func Positive_simple() {
	data := Source()
	Sink(data)
}

// PositiveWithEllipsis: intervening unrelated statement between source and sink.
func Positive_with_ellipsis() {
	data := Source()
	_ = data + " noop"
	Sink(data)
}

// PositiveIterProc: taint reaches Sink through an interprocedural wrapper.
func Positive_iter_proc() {
	data := Source()
	sinkWrapper(data)
}

func sinkWrapper(data string) {
	Sink(data)
}

// NegativeSimple: cleaner between Source and Sink drops the taint.
func Negative_simple() {
	data := Clean(Source())
	Sink(data)
}

// NegativeWithEllipsis: cleaner used in a longer flow with intervening stmts.
func Negative_with_ellipsis() {
	data := Source()
	_ = data + " noop"
	cleaned := Clean(data)
	Sink(cleaned)
}
