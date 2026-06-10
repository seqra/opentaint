package util

// Go port of example.RulePatternNotInsideWithSignature. The Java rule fires
// `sink($ARG)` when NOT inside a method with signature `$RET $METHOD(String $ARG)`.
// Recast in Go as plain source→sink — the signature constraint has no Go
// equivalent.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

func Positive_simple() {
	data := Source()
	Sink(data)
}

func Negative_constant() {
	Sink("unsafe")
}
