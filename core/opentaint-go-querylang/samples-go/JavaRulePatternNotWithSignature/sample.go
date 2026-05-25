package util

// Go port of example.RulePatternNotWithSignature. The Java rule fires when a
// method calls f($ARG) but NOT clean($ARG) before it. Recast in Go as
// Source -> F (sink) with Clean as a cleaner.
func Source() string         { return "tainted" }
func F(s string)             { _ = s }
func Clean(s string) string  { return s }

func Positive_simple() {
	data := Source()
	F(data)
}

func Negative_no_f() {
	_ = Source()
}

func Negative_clean_first() {
	data := Source()
	cleaned := Clean(data)
	F(cleaned)
}

// Positive_clean_after: cleaner runs AFTER sink — forward dataflow reports
// the sink anyway (mirrors the Java NegativeCleanSecond's IFDS behavior).
func Positive_clean_after() {
	data := Source()
	F(data)
	_ = Clean(data)
}
