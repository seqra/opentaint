package util

// Go port of example.RuleWithNotInsideDistinctReturnType. The Java rule
// uses two pattern-insides with different ResponseEntity<T> return types to
// filter methods. Go has no Java-style nominal generics; recast as plain
// source→sink (without the signature return-type scoping).
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

func Positive_simple() {
	d := Source()
	Sink(d)
}

func Negative_no_source() {
	Sink("safe")
}
