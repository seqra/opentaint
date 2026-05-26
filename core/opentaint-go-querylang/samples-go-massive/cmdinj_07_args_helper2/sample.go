package util

import (
	"os"
	"strings"
)

// Sink_ExecCommand represents a real os/exec.Command(...) call site (command injection sink).
func Sink_ExecCommand(cmd string) { _ = cmd }

func step1(s string) string { return strings.ToUpper(s) }
func step2(s string) string { return strings.TrimSpace(s) }

// Positive_twohop: os.Args -> step1 -> step2 -> sink.
func Positive_twohop() {
	v := step2(step1(os.Args[1]))
	Sink_ExecCommand("echo " + v)
}

// Negative_twohop_dropped: chain runs but result ignored.
func Negative_twohop_dropped() {
	_ = step2(step1(os.Args[1]))
	Sink_ExecCommand("echo hi")
}
