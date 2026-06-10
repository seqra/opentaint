package util

// Go port of example.RuleWithConcreteReturnType. The Java rule scopes the
// match by a method-signature whose return type is `String`. Go has no
// signature scoping; recast as plain source→sink.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

func Positive_simple() {
	d := Source()
	Sink(d)
}

func Negative_no_source() {
	Sink("safe")
}
