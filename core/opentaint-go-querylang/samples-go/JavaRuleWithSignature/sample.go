package util

// Go port of example.RuleWithSignature. The Java rule uses a pattern-either of
// sink1($A)/sink2($A) inside a method-signature constraint. Recast as
// source/sink-either, without the signature scoping.
func Source() string  { return "tainted" }
func Sink1(s string)  { _ = s }
func Sink2(s string)  { _ = s }

func Positive_sink1() {
	data := Source()
	Sink1(data)
}

func Positive_sink2() {
	data := Source()
	Sink2(data)
}

func Negative_no_source() {
	Sink1("safe")
}
