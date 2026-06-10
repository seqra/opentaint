package util

// Helpers used by the rule under test.
// Go port of example.RuleWithNotInsidePrefix: the Java rule says
// "match sink($X) except when prefixClean($X) appeared before it";
// in Go's taint mode this is a standard cleaner that wraps the source.
func Source() string             { return "tainted" }
func PrefixClean(s string) string { return s }
func Sink(s string)              { _ = s }

// Positive_simple: tainted source reaches sink with no cleaning.
func Positive_simple() {
	data := Source()
	Sink(data)
}

// Positive_clean_second: clean happens AFTER sink — sink is still tainted.
func Positive_clean_second() {
	data := Source()
	Sink(data)
	_ = PrefixClean(data)
}

// Positive_clean_on_other_data: clean on an unrelated tainted var; original taint reaches sink.
func Positive_clean_on_other_data() {
	data := Source()
	data1 := Source()
	_ = PrefixClean(data1)
	Sink(data)
}

// Negative_clean_first: prefix clean before sink drops the taint.
func Negative_clean_first() {
	data := Source()
	cleaned := PrefixClean(data)
	Sink(cleaned)
}
