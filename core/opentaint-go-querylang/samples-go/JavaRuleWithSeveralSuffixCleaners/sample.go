package util

// Helpers used by the rule under test.
// Go port of example.RuleWithSeveralSuffixCleaners — two distinct
// sanitizers either of which suppresses the sink.
func Source() string          { return "tainted" }
func Clean1(s string) string  { return s }
func Clean2(s string) string  { return s }
func F(s string)              { _ = s }

// Positive_simple: tainted source reaches sink with neither cleaner.
func Positive_simple() {
	data := Source()
	F(data)
}

// Negative_with_clean1: Clean1 sanitizes before sink.
func Negative_with_clean1() {
	data := Source()
	cleaned := Clean1(data)
	F(cleaned)
}

// Negative_with_clean2: Clean2 sanitizes before sink.
func Negative_with_clean2() {
	data := Source()
	cleaned := Clean2(data)
	F(cleaned)
}
