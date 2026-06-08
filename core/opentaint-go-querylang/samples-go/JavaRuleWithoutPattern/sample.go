package util

// Helpers used by the rule under test.
// Go port of example.RuleWithoutPattern. The Java rule has only a
// `pattern-inside: $RET $M(..., String $A, ...) { ... }` and no
// `pattern:` — every call site inside such a method matches. That
// shape (method-signature pattern-inside) is not expressible in Go
// (MethodEnter edges are dropped), so the port is recast as a normal
// taint rule that fires on Method($X) with a tainted-string argument.
// Go has overloading by name only via distinct identifiers; we use
// MethodStr / MethodInt to mimic Java's two `method(String)` /
// `method(int)` overloads.
func Source() string  { return "tainted" }
func Method(s string) { _ = s }   // string-arg variant — the targeted sink
func MethodInt(i int) { _ = i }   // int-arg variant — must not fire

// Positive_string_arg: tainted string flows into Method(string).
func Positive_string_arg() {
	data := Source()
	Method(data)
}

// Negative_int_arg: int-arg overload is not a sink at all.
func Negative_int_arg() {
	MethodInt(0)
}
