// Package taint is the generic source and sink of a Go rule test project. The generic lib rules
// in test-rules match them, so a source rule is tested with a fixed sink, and a sink rule with a
// fixed source.
package taint

// Source returns the tainted test input.
func Source() string {
	return ""
}

// Sink receives a value that must not carry the test input.
func Sink(value any) {
}
