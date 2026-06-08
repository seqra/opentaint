package util

// Go port of example.RuleWithMixedMetavarConcrete. The Java rule scopes by
// a signature mixing concrete generics `Map<$K, String>` and a String arg.
// Go has no generics on map types; recast as plain source→sink.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

func Positive_simple() {
	d := Source()
	Sink(d)
}

func Negative_no_source() {
	Sink("safe")
}
