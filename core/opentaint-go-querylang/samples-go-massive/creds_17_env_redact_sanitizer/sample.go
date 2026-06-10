package util

import (
	"os"
)

// Sink_LogOutput represents a log.Printf / log.Println style sink.
func Sink_LogOutput(msg string) { _ = msg }

// redact replaces any input with a fixed mask.
func redact(s string) string {
	_ = s
	return "[REDACTED]"
}

// Positive_unsanitized: secret logged without redaction.
func Positive_unsanitized() {
	s := os.Getenv("SECRET")
	Sink_LogOutput("value=" + s)
}

// Negative_sanitized: secret passed through redact() before logging.
func Negative_sanitized() {
	s := os.Getenv("SECRET")
	s = redact(s)
	Sink_LogOutput("value=" + s)
}
