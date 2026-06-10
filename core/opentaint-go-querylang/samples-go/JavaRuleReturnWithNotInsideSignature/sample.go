package util

// Go port of example.RuleReturnWithNotInsideSignature. The Java rule matches
// @EntryPoint methods that return $PARAM, except when the return is clean($PARAM).
// Recast in Go as source/clean/sink.
func Source() string         { return "tainted" }
func Clean(s string) string  { return s }
func Sink(s string)          { _ = s }

func Positive_simple() {
	r := method()
	Sink(r)
}

func method() string {
	o := Source()
	return o
}

func Negative_clean() {
	r := cleanedMethod()
	Sink(r)
}

func cleanedMethod() string {
	o := Source()
	return Clean(o)
}
