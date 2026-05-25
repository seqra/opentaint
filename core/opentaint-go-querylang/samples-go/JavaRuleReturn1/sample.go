package util

// Go port of example.RuleReturn1. Java rule: `return $X` inside `$X = src(); ...`
// matches any returned source-derived value. Recast as source/sink to verify
// the value flows out of the helper into a sink.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

func Positive_simple() {
	r := returned()
	Sink(r)
}

func returned() string {
	a := Source()
	return a
}

func Negative_constant_return() {
	r := constReturn()
	Sink(r)
}

func constReturn() string {
	_ = Source()
	return "safe"
}
