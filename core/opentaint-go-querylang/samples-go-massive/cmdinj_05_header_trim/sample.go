package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Sink_ExecLookPath represents a real os/exec.LookPath(...) call site (command injection sink).
func Sink_ExecLookPath(name string) { _ = name }

// Positive_trim: header trimmed then passed to LookPath.
func Positive_trim() {
	bin := strings.TrimSpace(r.Header.Get("X-Bin"))
	Sink_ExecLookPath(bin)
}

// Negative_skip: header read but unused.
func Negative_skip() {
	_ = strings.TrimSpace(r.Header.Get("X-Bin"))
	Sink_ExecLookPath("ls")
}
