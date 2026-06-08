package util

import (
	"os"
	"strings"
)

// Sink_ExecCommand represents a real os/exec.Command(...) call site (command injection sink).
func Sink_ExecCommand(cmd string) { _ = cmd }

func normalize(s string) string {
	return strings.ToLower(strings.TrimSpace(s))
}

func quote(s string) string {
	return "\"" + s + "\""
}

// Positive_fullchain: env -> normalize -> quote -> concat -> sink.
func Positive_fullchain() {
	v := quote(normalize(os.Getenv("X")))
	Sink_ExecCommand("printf " + v)
}

// Negative_fullchain_drop: pipeline runs but value discarded.
func Negative_fullchain_drop() {
	_ = quote(normalize(os.Getenv("X")))
	Sink_ExecCommand("printf hi")
}
