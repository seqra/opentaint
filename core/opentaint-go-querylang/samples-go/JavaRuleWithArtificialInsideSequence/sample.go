package util

// Go port of example.RuleWithArtificialInsideSequence. The Java rule fires
// `f($X)` when both `g($X)` and `h($X)` appeared first, but NOT after
// `clean($X)`. Recast in Go: G is a source-propagator (returns its argument
// as tainted) and Clean is a sanitizer; F is the sink. Because Go's
// forward dataflow is order-sensitive, we cannot encode "both g and h must
// precede f" without the AST-pattern engine; the Go port verifies the
// underlying taint flow shape.
func F(x string)             { _ = x }
func G(x string) string      { return x }
func H(x string) string      { return x }
func Clean(x string) string  { return x }

// Positive_simple: g taints x; sink fires.
func Positive_simple() {
	x := "data"
	tainted := G(x)
	tainted = H(tainted)
	F(tainted)
}

// Negative_with_clean: cleaner between source and sink drops taint.
func Negative_with_clean() {
	x := "data"
	tainted := G(x)
	cleaned := Clean(tainted)
	F(cleaned)
}

// Negative_no_g: never tainted, sink safe.
func Negative_no_g() {
	x := "data"
	F(x)
}
