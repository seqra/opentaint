package util

// Go port of example.RuleWithConcreteReturnDiscrim. The Java rule scopes by a
// 2-arg signature `String $METHOD(String $A, String $DATA)` and fires sink
// on $DATA (the 2nd arg). The signature constraint has no Go equivalent;
// recast as plain source→sink.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

func Positive_simple() {
	d := Source()
	Sink(d)
}

func Negative_no_source() {
	Sink("safe")
}
