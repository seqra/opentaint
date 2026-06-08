package util

// Go port of example.RuleReturn5. Identical semantics to RuleReturn4 in Java
// terms; the difference is the placement of `return $X` in the not-inside.
// Recast as source/clean/sink in Go.
func Source() string         { return "tainted" }
func Clean(s string) string  { return s }
func Sink(s string)          { _ = s }

func Positive_simple() {
	r := returned()
	Sink(r)
}

func returned() string {
	a := Source()
	return a
}

func Negative_cleaned() {
	r := cleanedReturned()
	Sink(r)
}

func cleanedReturned() string {
	a := Source()
	return Clean(a)
}
