package util

// Go port of example.RuleWithState. The Java rule fires "f(); g();" — a state-
// machine over the sequence. The Go pipeline expresses sequencing via taint
// propagation: F() returns a state token, G consumes it. Positive runs both
// in order; Negatives skip one.
func F() string    { return "fstate" }
func G(x string)   { _ = x }

func Positive_simple() {
	t := F()
	G(t)
}

func Negative_only_f() {
	_ = F()
}

func Negative_only_g() {
	G("safe")
}
