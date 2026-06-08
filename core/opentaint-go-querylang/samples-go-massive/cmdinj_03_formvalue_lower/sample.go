package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Sink_ExecBash represents a real exec.Command("bash", "-c", X) call site (command injection sink).
func Sink_ExecBash(cmd string) { _ = cmd }

// Positive_lower: FormValue lowercased then concat into bash -c arg.
func Positive_lower() {
	host := strings.ToLower(r.FormValue("host"))
	Sink_ExecBash("ping -c 1 " + host)
}

// Negative_static: source unused.
func Negative_static() {
	_ = r.FormValue("host")
	Sink_ExecBash("ping -c 1 127.0.0.1")
}
