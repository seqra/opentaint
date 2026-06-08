package util

// Helpers used by the rule under test.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

func Noop() { _ = "x" }

// Positive_with_intervening: assign source to x, run intervening stmts, then sink x.
func Positive_with_intervening() {
	var x string
	x = Source()
	Noop()
	Noop()
	Sink(x)
}

// Negative_no_sink: source assigned but never sinked.
func Negative_no_sink() {
	var x string
	x = Source()
	Noop()
	_ = x
}
