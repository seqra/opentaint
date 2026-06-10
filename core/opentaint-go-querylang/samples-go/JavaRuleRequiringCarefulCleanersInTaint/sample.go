package util

// Go port of example.RuleRequiringCarefulCleanersInTaint. The Java rule's
// pattern-sanitizer uses focus-metavariable to scope the sanitization to
// `$B = $A.getObjBad()`. In Go we drop the focus-metavariable and use a
// direct cleaner.
func Src() string                 { return "tainted" }
func GetObjGood(x string) string  { return x }
func GetObjBad(x string) string   { return x }
func Sink(s string)               { _ = s }

// Positive_simple: $B comes from GetObjGood; sink fires.
func Positive_simple() {
	a := Src()
	b := GetObjGood(a)
	Sink(b)
}

// Negative_bad: $B reassigned from GetObjBad — taint dropped.
func Negative_bad() {
	a := Src()
	b := GetObjGood(a)
	b = GetObjBad(a)
	Sink(b)
}
