package util

import (
	"os"
)

// Sink_LogOutput represents a log.Printf / log.Println style sink.
func Sink_LogOutput(msg string) { _ = msg }

// Positive_defer_log: deferred log call exposes SLACK_TOKEN.
func Positive_defer_log() {
	t := os.Getenv("SLACK_TOKEN")
	defer Sink_LogOutput("exit with slack token=" + t)
}

// Negative_defer_log_const: deferred log call uses constant string.
func Negative_defer_log_const() {
	_ = os.Getenv("SLACK_TOKEN")
	defer Sink_LogOutput("exit done")
}
