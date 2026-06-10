package util

// Go port of example.JoinWithTaintAndMatchingLeft. The Java rule is a join
// rule with two independent rules joined on a common sink metavariable.
// Go's pipeline does not implement `mode: join`; we recast the taint side
// of the join as a single taint-mode rule with two propagator steps.
func GetUntrustedInput() string         { return "untrusted" }
func ProcessInput(x string) string      { return x }
func TransformData(x string) string     { return x }
func ExecuteDangerous(x string)         { _ = x }
func CreateInitialData() string         { return "init" }

// Positive_taint_flow: untrusted → process → transform → dangerous exec.
func Positive_taint_flow() {
	untrusted := GetUntrustedInput()
	processed := ProcessInput(untrusted)
	result := TransformData(processed)
	ExecuteDangerous(result)
}

// Negative_missing_untrusted: chain starts with constant; no taint.
func Negative_missing_untrusted() {
	safe := "safe"
	processed := ProcessInput(safe)
	result := TransformData(processed)
	ExecuteDangerous(result)
}

// Negative_no_sink: source created but never reaches ExecuteDangerous.
func Negative_no_sink() {
	data := CreateInitialData()
	_ = data
}
