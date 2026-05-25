package util

// Go port of example.RuleWithAnyPattern. The Java rule uses `pattern: ...`
// (matches any expression) inside a method-signature scope. There is no Go
// equivalent for "any expression" matching — the Go port reduces this to a
// source/sink flow on the string-arg overload of method.
func Source() string  { return "tainted" }
func Method(s string) { _ = s }
func MethodInt(i int) { _ = i }

func Positive_simple() {
	d := Source()
	Method(d)
}

func Negative_int_arg() {
	MethodInt(0)
}
