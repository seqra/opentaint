package util

import (
	"os"
	"strconv"
)

// Sink_ExecCommand represents a real os/exec.Command(...) call site (command injection sink).
func Sink_ExecCommand(cmd string) { _ = cmd }

// Positive_directstring: tainted string concat directly.
func Positive_directstring() {
	s := os.Args[1]
	Sink_ExecCommand("kill " + s)
}

// Negative_atoi: strconv.Atoi converts to int; taint considered lost.
func Negative_atoi() {
	n, _ := strconv.Atoi(os.Args[1])
	_ = n
	Sink_ExecCommand("kill 1")
}
