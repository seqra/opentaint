package util

// Go port of example.RuleWithArtificialInsideSequenceReverse. The Java rule
// fires `f($X)` when both `g($X)` and `h($X)` follow (suffix), but NOT if
// `clean($X)` came after f. Recast in Go: F is a source-propagator and
// H is the sink (forward dataflow direction); Clean sanitizes between.
func F(x string) string      { return x }
func G(x string) string      { return x }
func H(x string)             { _ = x }
func Clean(x string) string  { return x }

func Positive_simple() {
	x := "data"
	tainted := F(x)
	tainted = G(tainted)
	H(tainted)
}

func Negative_with_clean() {
	x := "data"
	tainted := F(x)
	cleaned := Clean(tainted)
	H(cleaned)
}

func Negative_no_f() {
	x := "data"
	H(x)
}
