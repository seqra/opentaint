package util

// Helpers used by the rule under test.
// Go port of example.RuleWithSimplePass. The Java rule uses `pass($A, $B)`
// with `pattern-either` covering several intersection shapes; the closest
// Go-taint construct is a propagator that carries taint from input to
// output via the return value (the by-side-effect arg form isn't yet
// expressible in the Go pipeline — see NilCheck @Disabled).
func Source() string         { return "tainted" }
func Pass(in string) string  { return in }
func Sink(s string)          { _ = s }

// Positive_simple: Pass propagates taint into other, then sink fires on other.
func Positive_simple() {
	data := Source()
	other := Pass(data)
	Sink(other)
}

// Negative_no_pass: Pass isn't used; sink is called with a constant.
func Negative_no_pass() {
	data := Source()
	_ = data
	Sink("constant")
}
