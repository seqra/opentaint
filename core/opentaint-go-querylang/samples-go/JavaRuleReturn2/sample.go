package util

// Go port of example.RuleReturn2. Java rule: `return $X` with `pattern-not-inside:
// clean($X)`. Recast as Source/Clean/Sink in Go.
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
