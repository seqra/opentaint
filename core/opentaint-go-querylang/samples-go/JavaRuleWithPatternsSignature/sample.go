package util

// Go port of example.RuleWithPatternsSignature. The Java rule uses a method
// signature pattern AND a `sink($A)` call pattern. Recast in Go as source/sink.
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
