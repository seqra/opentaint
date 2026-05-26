package util

import (
	"os"
)

// Sink_ExecCommand represents a real os/exec.Command(...) call site (command injection sink).
func Sink_ExecCommand(cmd string) { _ = cmd }

// Positive_defer: defer wraps the sink with tainted env.
func Positive_defer() {
	w := os.Getenv("WORK")
	defer Sink_ExecCommand("cleanup " + w)
}

// Negative_defer_const: defer sinks but no tainted data.
func Negative_defer_const() {
	_ = os.Getenv("WORK")
	defer Sink_ExecCommand("cleanup default")
}
