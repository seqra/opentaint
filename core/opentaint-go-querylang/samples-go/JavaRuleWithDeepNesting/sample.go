package util

// Go port of example.RuleWithDeepNesting. The Java rule scopes by a method
// signature with a deeply-nested generic return type `List<List<String>>`.
// Go has no generic List<List<>>; recast as plain source→sink.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

func Positive_simple() {
	d := Source()
	Sink(d)
}

func Negative_no_source() {
	Sink("safe")
}
