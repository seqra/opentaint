package util

import (
	"os"
)

// Positive_basic: env value concatenated into a path and opened.
func Positive_basic() {
	name := os.Getenv("FILE")
	f, _ := os.Open("/var/data/" + name)
	_ = f
}

// Negative_const: env read but constant path opened.
func Negative_const() {
	_ = os.Getenv("FILE")
	f, _ := os.Open("/var/data/static.txt")
	_ = f
}
