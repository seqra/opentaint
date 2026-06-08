package util

import (
	"fmt"
	"os"
)

// Sink_LogError represents a real log/error sink that exposes the message.
func Sink_LogError(msg string) { _ = msg }

// Positive_errorf: API key embedded into an error message and logged.
func Positive_errorf() {
	k := os.Getenv("API_KEY")
	err := fmt.Errorf("auth failed using key %s", k)
	Sink_LogError(err.Error())
}

// Positive_errorf_wrap: API key passed through fmt.Errorf wrapping then sunk.
func Positive_errorf_wrap() {
	k := os.Getenv("API_KEY")
	err := fmt.Errorf("rejected: %s", k)
	Sink_LogError(err.Error())
}

// Negative_const: API_KEY read but a constant error message is logged.
func Negative_const() {
	_ = os.Getenv("API_KEY")
	err := fmt.Errorf("auth failed")
	Sink_LogError(err.Error())
}
