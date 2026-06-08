package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Sink_ExecBash represents a real exec.Command("bash", "-c", X) call site (command injection sink).
func Sink_ExecBash(cmd string) { _ = cmd }

// Positive_trim: URL query trimmed then concat.
func Positive_trim() {
	s := strings.Trim(r.URL.Query().Get("s"), " ")
	Sink_ExecBash("grep " + s + " /tmp/x")
}

// Negative_trim_unused: trimmed value ignored.
func Negative_trim_unused() {
	_ = strings.Trim(r.URL.Query().Get("s"), " ")
	Sink_ExecBash("grep foo /tmp/x")
}
