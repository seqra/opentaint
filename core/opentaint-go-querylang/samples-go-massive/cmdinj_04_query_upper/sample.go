package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Sink_ExecCommand represents a real os/exec.Command(...) call site (command injection sink).
func Sink_ExecCommand(cmd string) { _ = cmd }

// Positive_upper: URL query upcased then concat.
func Positive_upper() {
	target := strings.ToUpper(r.URL.Query().Get("target"))
	Sink_ExecCommand("nslookup " + target)
}

// Negative_drop: source consumed but result not used.
func Negative_drop() {
	_ = strings.ToUpper(r.URL.Query().Get("target"))
	Sink_ExecCommand("nslookup example.com")
}
