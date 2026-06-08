package util

// Go port of example.R3. The Java rule layers `$RET = bar($X)` inside a
// `pattern-inside: $X = foo($ARG)` with a `pattern-not: $X = $F($ARG); ...`.
// Recast as: util.Source -> arg -> util.Bar (sink).
func Source() string         { return "tainted" }
func Bar(s string) string    { return s }

func Positive_simple() {
	x := Source()
	_ = Bar(x)
}
