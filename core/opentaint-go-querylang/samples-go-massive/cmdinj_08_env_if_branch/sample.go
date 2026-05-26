package util

import (
	"os"
)

// Sink_ExecCommand represents a real os/exec.Command(...) call site (command injection sink).
func Sink_ExecCommand(cmd string) { _ = cmd }

// Positive_branchsink: only one branch sinks tainted value.
func Positive_branchsink() {
	a := os.Getenv("ACTION")
	if len(a) > 0 {
		Sink_ExecCommand("run " + a)
	} else {
		Sink_ExecCommand("run default")
	}
}

// Negative_otherbranch: tainted reaches sink in non-tainting branch.
func Negative_otherbranch() {
	a := os.Getenv("ACTION")
	if len(a) > 0 {
		_ = a
		Sink_ExecCommand("run default")
	} else {
		Sink_ExecCommand("run idle")
	}
}
