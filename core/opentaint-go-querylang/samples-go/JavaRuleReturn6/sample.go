package util

// Go port of example.RuleReturn6. Java rule's intent: source value is locally
// assigned but never returned. In Go, recast as plain source-to-sink.
func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

// Positive_simple: source flows into sink.
func Positive_simple() {
	a := Source()
	Sink(a)
}

// Negative_unused: source produced but never reaches sink.
func Negative_unused() {
	_ = Source()
}
