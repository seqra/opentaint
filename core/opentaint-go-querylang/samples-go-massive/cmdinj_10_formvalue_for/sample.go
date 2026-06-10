package util

import (
	"net/http"
)

var r *http.Request

// Sink_ExecCommand represents a real os/exec.Command(...) call site (command injection sink).
func Sink_ExecCommand(cmd string) { _ = cmd }

// Positive_for: tainted used in per-iteration sink.
func Positive_for() {
	hosts := []string{"a", "b", "c"}
	flag := r.FormValue("flag")
	for _, h := range hosts {
		Sink_ExecCommand("ping " + flag + " " + h)
	}
}

// Negative_for_const: source not propagated.
func Negative_for_const() {
	hosts := []string{"a", "b", "c"}
	_ = r.FormValue("flag")
	for _, h := range hosts {
		Sink_ExecCommand("ping " + h)
	}
}
