package util

import (
	"os"
	"strings"
)

// Sink_ExecCommand represents a real os/exec.Command(...) call site (command injection sink).
func Sink_ExecCommand(cmd string) { _ = cmd }

func shellEscape(s string) string {
	return strings.ReplaceAll(s, "'", "")
}

// Positive_branch_one_clean: one branch sanitizes, other does not.
func Positive_branch_one_clean() {
	a := os.Getenv("ARG")
	if len(a) > 8 {
		clean := shellEscape(a)
		Sink_ExecCommand("tool " + clean)
	} else {
		Sink_ExecCommand("tool " + a)
	}
}

// Negative_branch_clean: tainted always sanitized.
func Negative_branch_clean() {
	a := os.Getenv("ARG")
	clean := shellEscape(a)
	Sink_ExecCommand("tool " + clean)
}
