package util

import (
	"os"
)

// Sink_ExecBash represents a real exec.Command("bash", "-c", X) call site (command injection sink).
func Sink_ExecBash(cmd string) { _ = cmd }

// Positive_switch: tainted matches and sinks in all case branches.
func Positive_switch() {
	a := os.Args[1]
	switch a {
	case "ls":
		Sink_ExecBash("ls " + a)
	default:
		Sink_ExecBash("echo " + a)
	}
}

// Negative_switch_const: switch ignores value of tainted past matching.
func Negative_switch_const() {
	a := os.Args[1]
	switch a {
	case "ls":
		Sink_ExecBash("ls /tmp")
	default:
		Sink_ExecBash("echo done")
	}
}
