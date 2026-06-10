package util

// Go port of example.RuleRequiringCarefulCleaners. The Java rule fires when
// $A = src(); $B = $A.getObjGood(); sink($B), but NOT when $B = $A.getObjBad().
// Recast in Go: GetObjGood is the source; GetObjBad is a sanitizer (i.e. the
// value coming out of GetObjBad replaces a previously-tainted $B).
func Src() string                { return "x" }
func GetObjGood(x string) string { return x }
func GetObjBad(x string) string  { return x }
func Sink(s string)              { _ = s }

// Positive_simple: value comes from GetObjGood (source) → sink.
func Positive_simple() {
	a := Src()
	b := GetObjGood(a)
	Sink(b)
}

// Negative_bad: $B is replaced by GetObjBad (sanitizer) — taint dropped.
func Negative_bad() {
	a := Src()
	b := GetObjGood(a)
	b = GetObjBad(a)
	Sink(b)
}
