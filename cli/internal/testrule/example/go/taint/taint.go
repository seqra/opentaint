// Package taint is the generic taint marker of a Go rule test project. Source returns a string
// and Sink accepts any value. The bundled generic-source / generic-sink lib rules match them, so
// a package's source/sink lib rules can be exercised against a fixed counterpart.
package taint

// Source returns the tainted test input.
func Source() string {
	return ""
}

// Sink receives a value that must not carry the test input.
func Sink(value any) {
}
