package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Sink_ExecCommand represents a real os/exec.Command(...) call site (command injection sink).
func Sink_ExecCommand(cmd string) { _ = cmd }

// Positive_unsanitized: header concat into command without sanitizer.
func Positive_unsanitized() {
	h := r.Header.Get("X-Cmd")
	Sink_ExecCommand("run " + h)
}

// Negative_sanitized: tainted header passed through ReplaceAll sanitizer.
func Negative_sanitized() {
	h := r.Header.Get("X-Cmd")
	h = strings.ReplaceAll(h, ";", "")
	Sink_ExecCommand("run " + h)
}
