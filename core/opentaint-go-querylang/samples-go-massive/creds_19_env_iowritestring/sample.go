package util

import (
	"io"
	"os"
)

var f *os.File

// Positive_iowritestring: VAULT_TOKEN written to file via io.WriteString.
func Positive_iowritestring() {
	t := os.Getenv("VAULT_TOKEN")
	_, _ = io.WriteString(f, "vault="+t)
}

// Negative_iowritestring_const: env read but constant string written.
func Negative_iowritestring_const() {
	_ = os.Getenv("VAULT_TOKEN")
	_, _ = io.WriteString(f, "vault=<redacted>")
}
