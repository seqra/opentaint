package util

// Go port of example.RuleWithMultiplePatternsUnification. The Java rule
// requires both `$SOURCE.mkType2()` AND `new CustomType3($SOURCE)` to appear,
// then returns the latter. Recast in Go using forward taint flow: MkType2 is
// a source returning a tainted value; NewType3 is a sink that consumes it.
func MkType2(s string) string  { return s }
func NewType3(s string) string { return s }

// Positive_simple: tainted value from MkType2 flows into NewType3.
func Positive_simple() string {
	src := "x"
	v2 := MkType2(src)
	sink := NewType3(v2)
	return sink
}

// Negative_no_mkType2: no MkType2 source called; sink on raw value is safe.
func Negative_no_mkType2() string {
	src := "x"
	return NewType3(src)
}
