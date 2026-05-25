package util

// Go port of example.RuleWithEllipsisInvocationAndPatternNot. The Java rule
// matches: src() → A.getObjGood().toString() → sink, but excludes the
// getObjBad variant. Recast in Go: Src is the source, GetObjGood is a
// pass-through (allowed); GetObjBad is a sanitizer (suppresses).
func Src() string                    { return "tainted" }
func GetObjGood(x string) string     { return x }
func GetObjBad(x string) string      { return x }
func Sink(s string)                  { _ = s }

func Positive_simple() {
	d := Src()
	s := GetObjGood(d)
	Sink(s)
}

func Negative_bad_path() {
	d := Src()
	s := GetObjBad(d)
	Sink(s)
}
