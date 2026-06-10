package util

import (
	"os"
	"strings"
)

// Sink_ExecCommand represents a real os/exec.Command(...) call site (command injection sink).
func Sink_ExecCommand(cmd string) { _ = cmd }

func normalize(s string) string {
	return strings.ToLower(s)
}

// Positive_helper1: env normalized via helper then concat into command.
func Positive_helper1() {
	t := normalize(os.Getenv("TOOL"))
	Sink_ExecCommand("which " + t)
}

// Negative_helperdrop: helper called, result ignored.
func Negative_helperdrop() {
	_ = normalize(os.Getenv("TOOL"))
	Sink_ExecCommand("which sh")
}
