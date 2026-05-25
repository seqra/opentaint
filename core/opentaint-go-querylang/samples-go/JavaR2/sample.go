package util

// Go port of example.R2. Java rule layers pattern + pattern-not + pattern-inside
// + pattern-not-inside around a `return foo($ARG)` shape. Recast in Go as the
// underlying source -> return -> sink taint-flow it expresses.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

func Positive_simple() {
	x := method()
	Sink(x)
}

func method() string {
	x := Source()
	return x
}
