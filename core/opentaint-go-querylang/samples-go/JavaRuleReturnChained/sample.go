package util

// Go port of example.RuleReturnChained. Java rule expects to match a chain
// `src.mkType2().mkType3().mkType1()` returned from a method taking a
// `CustomType1`. Go has no nominal types like this, so the rule is recast
// to function-call sources/sinks operating on a value chain.
func MkType2(s string) string { return s }
func MkType3(s string) string { return s }
func MkType1(s string) string { return s }

func Positive_simple() string {
	src := "x"
	v3 := MkType3(MkType2(src))
	sink := MkType1(v3)
	return sink
}

func Positive_one_line() string {
	return MkType1(MkType3(MkType2("x")))
}

// Negative: return halts before MkType1 — no sink call.
func Negative_no_mkType1() string {
	return MkType3(MkType2("x"))
}
