package util

import (
	"os"
)

// Positive_defer: tainted env captured in a defer that calls os.Remove.
func Positive_defer() {
	name := os.Getenv("TMP_FILE")
	p := "/tmp/" + name
	defer os.Remove(p)
	// ... pretend work ...
}

// Negative_const_defer: env read but defer removes a constant path.
func Negative_const_defer() {
	_ = os.Getenv("TMP_FILE")
	defer os.Remove("/tmp/static.tmp")
}
