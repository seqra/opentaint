package util

// Go port of example.RuleReturnNotInsidePrefix. The Java rule fires when an
// `s.mkType3().mkType1()` is returned but `s.clean()` was NOT called before.
// Recast as MkType2 -> MkType1 with Clean as a sanitizer.
func MkType2(x string) string { return x }
func MkType3(x string) string { return x }
func MkType1(x string) string { return x }
func Clean(x string) string   { return x }

func Positive_simple() string {
	s := MkType2("x")
	return MkType1(MkType3(s))
}

func Negative_with_clean() string {
	s := MkType2("x")
	cleaned := Clean(s)
	return MkType1(MkType3(cleaned))
}
