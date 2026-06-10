package util

// Go port of example.RuleWithMultiplePatternsEllipsisUnification. The Java
// rule chains three patterns with ellipsis between each step, joined by
// metavariable unification. Recast in Go as MkType2 (source) → MkType3
// (transparent propagator) → MkType1FromType3 (sink).
func MkType2(s string) string             { return s }
func MkType3(s string) string             { return s }
func MkType1FromType3(s string) string    { return s }

func Positive_simple() string {
	src := "x"
	v2 := MkType2(src)
	v3 := MkType3(v2)
	sink := MkType1FromType3(v3)
	return sink
}
