package util

// Go port of example.RuleWithPatternsSimple. The Java rule combines:
//   `$A = src(); ...` AND `...; sink($A);` — basic source-to-sink. Direct.
func Source() string  { return "tainted" }
func Sink(s string)   { _ = s }
func Other(s string)  { _ = s }

func Positive_simple() {
	src := Source()
	Sink(src)
}

func Negative_other_sink() {
	src := Source()
	Other(src)
}

func Negative_no_source() {
	Sink("safe")
}
