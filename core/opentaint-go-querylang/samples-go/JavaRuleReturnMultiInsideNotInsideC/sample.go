package util

// Go port of example.RuleReturnMultiInsideNotInsideC. Java rule: source via
// $SOURCE.mkType2() → mkType3(); pattern-not-inside sanitizeC($T1) or
// sanitizeC($SINK). Recast in Go: MkType2 source → MkType3 sink with
// SanitizeC cleaner (returning the cleaned value).
func MkType2(x string) string   { return x }
func MkType3(x string) string   { return x }
func SanitizeC(x string) string { return x }

func Positive_simple() string {
	t1 := MkType2("x")
	return MkType3(t1)
}

func Negative_clean_t1() string {
	t1 := MkType2("x")
	cleaned := SanitizeC(t1)
	return MkType3(cleaned)
}

// Positive2: another (unrelated) value gets sanitized — taint on t1 reaches
// MkType3 unaffected.
func Positive2_sanitize_other() string {
	t1 := MkType2("x")
	_ = SanitizeC("other")
	return MkType3(t1)
}
