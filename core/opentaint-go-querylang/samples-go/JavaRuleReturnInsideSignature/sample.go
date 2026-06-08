package util

// Go port of example.RuleReturnInsideSignature. Java rule scopes the match by
// method signature `$RET $METHOD(String $ARG)`. Go has no equivalent of Java
// nominal signatures — we drop the signature constraint and verify the
// underlying source/sink flow.
func Src(s string) string { return s }
func Sink(s string)       { _ = s }

func Positive_simple() {
	a := Src("data")
	Sink(a)
}

func Negative_no_src() {
	Sink("safe")
}
