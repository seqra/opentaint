package util

import (
	"net/http"
	"regexp"
)

var r *http.Request

// Sink_ExecCommand represents a real os/exec.Command(...) call site (command injection sink).
func Sink_ExecCommand(cmd string) { _ = cmd }

// Positive_noregex: tainted FormValue concat without sanitizer.
func Positive_noregex() {
	v := r.FormValue("v")
	Sink_ExecCommand("show " + v)
}

// Negative_regex_sanitized: regex sanitizer strips non-alnum chars.
func Negative_regex_sanitized() {
	v := r.FormValue("v")
	clean := regexp.MustCompile(`[^a-zA-Z0-9]`).ReplaceAllString(v, "")
	Sink_ExecCommand("show " + clean)
}
