package util

import (
	"os"
)

// Sink_LogOutput represents a log.Printf / log.Println style sink.
func Sink_LogOutput(msg string) { _ = msg }

// wrapMessage prefixes a value with a fixed label.
func wrapMessage(inner string) string {
	return "[stripe-key] " + inner
}

// Positive_helper_chain: env -> wrapMessage -> log sink.
func Positive_helper_chain() {
	k := os.Getenv("STRIPE_KEY")
	m := wrapMessage(k)
	Sink_LogOutput(m)
}

// Negative_helper_const: helper called with a constant, env unused.
func Negative_helper_const() {
	_ = os.Getenv("STRIPE_KEY")
	m := wrapMessage("redacted")
	Sink_LogOutput(m)
}
