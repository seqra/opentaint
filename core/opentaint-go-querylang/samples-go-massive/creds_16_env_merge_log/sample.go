package util

import (
	"os"
)

// Sink_LogOutput represents a log.Printf / log.Println style sink.
func Sink_LogOutput(msg string) { _ = msg }

// Positive_merge_log: DB_USER and DB_PASS concatenated into one log line.
func Positive_merge_log() {
	u := os.Getenv("DB_USER")
	p := os.Getenv("DB_PASS")
	Sink_LogOutput("user=" + u + " pass=" + p)
}

// Negative_merge_log_unused: both env vars read but constant logged.
func Negative_merge_log_unused() {
	_ = os.Getenv("DB_USER")
	_ = os.Getenv("DB_PASS")
	Sink_LogOutput("user=*** pass=***")
}
