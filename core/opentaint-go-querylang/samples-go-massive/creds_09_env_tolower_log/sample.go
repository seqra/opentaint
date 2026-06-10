package util

import (
	"os"
	"strings"
)

// Sink_LogOutput represents a log.Printf / log.Println style sink.
func Sink_LogOutput(msg string) { _ = msg }

// Positive_tolower: API_TOKEN normalized via strings.ToLower then logged.
func Positive_tolower() {
	t := os.Getenv("API_TOKEN")
	lc := strings.ToLower(t)
	Sink_LogOutput("token=" + lc)
}

// Negative_tolower_const: env read but ToLower applied to a constant value.
func Negative_tolower_const() {
	_ = os.Getenv("API_TOKEN")
	lc := strings.ToLower("STATIC")
	Sink_LogOutput("token=" + lc)
}
