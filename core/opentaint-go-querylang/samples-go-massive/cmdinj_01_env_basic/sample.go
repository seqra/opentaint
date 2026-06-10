package util

import (
	"os"
)

// Sink_ExecCommand represents a real os/exec.Command(...) call site (command injection sink).
func Sink_ExecCommand(cmd string) { _ = cmd }

// Positive_basic: env concatenated into shell-like command string.
func Positive_basic() {
	c := os.Getenv("CMD")
	Sink_ExecCommand("ls " + c)
}

// Negative_const: env read but constant runs.
func Negative_const() {
	_ = os.Getenv("CMD")
	Sink_ExecCommand("ls /tmp")
}
