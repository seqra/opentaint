package util

// Helpers used by the rule under test.
// Go port of example.RuleReturnSimple. The Java rule is a method-signature
// pattern `$RETURNTYPE $M(..., CustomType1 $S, ...) { ... return $S; }`
// which the Go pipeline cannot express (MethodEnter/MethodExit edges are
// dropped — see GoTaintRuleGeneration). The Go port preserves the test
// fixture's *spirit*: an interprocedural helper `simple` that returns its
// argument directly. The rule itself collapses to call-based source/sink.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

// Positive: helper returns its source-derived argument; sink consumes the return.
func Positive_returns_source() {
	Sink(simple(Source()))
}

func simple(src string) string {
	ret := src
	return ret
}

// Negative: helper returns a fresh safe value; the source argument is discarded.
func Negative_returns_safe() {
	Sink(safeHelper(Source()))
}

func safeHelper(src string) string {
	_ = src
	return "safe"
}
