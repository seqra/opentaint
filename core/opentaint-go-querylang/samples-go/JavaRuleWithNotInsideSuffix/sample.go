package util

// Helpers used by the rule under test.
// Go port of example.RuleWithNotInsideSuffix. The Java rule does
// `pattern-not-inside: ... ; suffixClean($X)` so the clean is required
// AFTER the sink to suppress.
func Source() string              { return "tainted" }
func SuffixClean(s string) string { return s }
func Sink(s string)               { _ = s }

// Positive_simple: bare source-to-sink, no clean of any kind.
func Positive_simple() {
	data := Source()
	Sink(data)
}

// Positive_clean_first: clean happens BEFORE sink — the Java rule's
// suffix-clean would NOT suppress (clean must follow). In Go's
// dataflow model, however, clean-before-sink does drop the taint;
// so this case diverges from Java. The Go sample-based test treats
// the rule as a normal cleaner — clean-before-sink → no vulnerability.
func Negative_clean_first() {
	data := Source()
	cleaned := SuffixClean(data)
	Sink(cleaned)
}

// Positive_clean_on_other_data: clean is on a different variable.
func Positive_clean_on_other_data() {
	data := Source()
	data1 := Source()
	Sink(data)
	_ = SuffixClean(data1)
}

// Positive_clean_second: clean follows the sink — Java would treat it
// as a suppressor; Go's dataflow cleaner runs forward and only sees the
// sink first, so the taint at the sink remains.
func Positive_clean_second() {
	data := Source()
	Sink(data)
	_ = SuffixClean(data)
}
