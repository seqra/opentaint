package util

import (
	"net/http"
)

var r *http.Request

// Sink_ExecBash represents a real exec.Command("bash", "-c", X) call site (command injection sink).
func Sink_ExecBash(cmd string) { _ = cmd }

// Positive_closure: tainted captured by closure then sinked.
func Positive_closure() {
	q := r.URL.Query().Get("q")
	fn := func() {
		Sink_ExecBash("echo " + q + " | wc")
	}
	fn()
}

// Negative_closure_unused: closure captures but does not use tainted.
func Negative_closure_unused() {
	q := r.URL.Query().Get("q")
	_ = q
	fn := func() {
		Sink_ExecBash("echo hi | wc")
	}
	fn()
}
