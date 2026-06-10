package util

import (
	"os"
)

// Sink_LogOutput represents a log.Printf / log.Println style sink.
func Sink_LogOutput(msg string) { _ = msg }

// Positive_closure_log: closure captures tainted secret and logs it.
func Positive_closure_log() {
	k := os.Getenv("GCP_KEY")
	fn := func() {
		Sink_LogOutput("gcp key=" + k)
	}
	fn()
}

// Negative_closure_log_unused: closure captures secret but doesn't log it.
func Negative_closure_log_unused() {
	k := os.Getenv("GCP_KEY")
	_ = k
	fn := func() {
		Sink_LogOutput("gcp loaded")
	}
	fn()
}
