package util

// Go port of example.RuleWithType. The Java rule scopes a method call by
// receiver type via a type cast: `(SimpleType $O).foo()` vs `(OtherType $O).foo()`.
// Go has no equivalent cast-pattern; we recast by using distinct function names
// per type (FooSimple vs FooOther) to verify the source/sink wiring is correct.
func MakeSimple() string { return "simple" }
func MakeOther() string  { return "other" }
func FooSimple(s string) { _ = s }
func FooOther(s string)  { _ = s }

func Positive_simple() {
	s := MakeSimple()
	FooSimple(s)
}

// Negative_other_type: different sink — no match.
func Negative_other_type() {
	s := MakeOther()
	FooOther(s)
}
