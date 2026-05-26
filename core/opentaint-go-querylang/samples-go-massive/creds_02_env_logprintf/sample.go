package util

import (
	"fmt"
	"os"
)

// Sink_LogOutput represents a real log.Printf / log.Println style output sink.
func Sink_LogOutput(msg string) { _ = msg }

// Positive_logprintf: DB password concatenated into log message.
func Positive_logprintf() {
	p := os.Getenv("DB_PASS")
	Sink_LogOutput("connecting with pass=" + p)
}

// Positive_sprintf: DB password formatted via Sprintf then logged.
func Positive_sprintf() {
	p := os.Getenv("DB_PASS")
	line := fmt.Sprintf("db login pass=%s", p)
	Sink_LogOutput(line)
}

// Negative_const: env read, but constant string logged.
func Negative_const() {
	_ = os.Getenv("DB_PASS")
	Sink_LogOutput("connecting with pass=***")
}
