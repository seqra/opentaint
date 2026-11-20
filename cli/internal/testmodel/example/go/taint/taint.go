// Package taint is the fixed source and sink of a Go model test project.
package taint

// Source returns the tainted test input.
func Source() string {
	return ""
}

// Sink receives a value that must not carry the test input.
func Sink(value string) {
}
