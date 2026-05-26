package util

import (
	"fmt"
	"os"
)

// Sink_LogOutput represents a log.Printf / log.Println style sink.
func Sink_LogOutput(msg string) { _ = msg }

// Positive_variadic_sprintf: REFRESH_TOKEN passed as one of several variadic Sprintf args.
func Positive_variadic_sprintf() {
	t := os.Getenv("REFRESH_TOKEN")
	line := fmt.Sprintf("user=%s refresh=%s ts=%s", "alice", t, "now")
	Sink_LogOutput(line)
}

// Positive_variadic_sprintf_first: REFRESH_TOKEN in first position of multi-arg Sprintf.
func Positive_variadic_sprintf_first() {
	t := os.Getenv("REFRESH_TOKEN")
	line := fmt.Sprintf("refresh=%s id=%s", t, "u-1")
	Sink_LogOutput(line)
}

// Negative_variadic_sprintf_unused: env read but not substituted into format.
func Negative_variadic_sprintf_unused() {
	_ = os.Getenv("REFRESH_TOKEN")
	line := fmt.Sprintf("user=%s refresh=%s ts=%s", "alice", "***", "now")
	Sink_LogOutput(line)
}
