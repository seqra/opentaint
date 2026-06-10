package util

// Go port of example.RuleReturnMultiInsideNotInsideA. Java rule: source via
// $SOURCE.mkType2(); pass to mkType3(); pattern-not-inside sanitizeA($SINK).
// Recast as MkType2 source → MkType3 sink with SanitizeA cleaner. The Go
// sanitizer returns the cleaned value (forward-dataflow friendly).
func MkType2(x string) string   { return x }
func MkType3(x string) string   { return x }
func SanitizeA(x string) string { return x }

func Positive_simple() string {
	v2 := MkType2("x")
	return MkType3(v2)
}

func Negative_with_sanitize() string {
	v2 := MkType2("x")
	cleaned := SanitizeA(v2)
	return MkType3(cleaned)
}
