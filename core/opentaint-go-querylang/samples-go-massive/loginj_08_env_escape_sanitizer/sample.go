package util

import (
	"log"
	"os"
	"strings"
)

// escapeNewlines strips CR/LF characters that could forge fake log lines.
func escapeNewlines(s string) string {
	s = strings.ReplaceAll(s, "\n", " ")
	s = strings.ReplaceAll(s, "\r", " ")
	return s
}

// Positive_unsanitized: env reaches log.Printf without escaping newlines.
func Positive_unsanitized() {
	u := os.Getenv("TRACE_ID")
	log.Printf("trace=%s", u)
}

// Negative_sanitized: tainted env passed through escapeNewlines sanitizer.
func Negative_sanitized() {
	u := os.Getenv("TRACE_ID")
	u = escapeNewlines(u)
	log.Printf("trace=%s", u)
}
