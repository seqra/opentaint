package util

// Go port of example.R1. Java rule selects `return $X` where $X = foo($ARG)
// but $METHOD's parameter is NOT `Object $ARG` (i.e., $ARG isn't the input).
// Recast as a standard taint flow: util.Source() -> ret -> util.Sink.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

// Positive: source -> return -> sink.
func Positive_simple() {
	r := method()
	Sink(r)
}

func method() string {
	x := Source()
	return x
}

// Negative: returned value is a constant, no taint.
func Negative_no_source() {
	r := constMethod()
	Sink(r)
}

func constMethod() string {
	return "safe"
}
