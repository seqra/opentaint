package util

import (
	"net/http"
)

var r *http.Request

// Sink_LogOutput represents a log.Print style output sink.
func Sink_LogOutput(msg string) { _ = msg }

// Positive_auth_log: Authorization header value logged.
func Positive_auth_log() {
	a := r.Header.Get("Authorization")
	Sink_LogOutput("request authz=" + a)
}

// Negative_auth_log_const: header read but constant string logged.
func Negative_auth_log_const() {
	_ = r.Header.Get("Authorization")
	Sink_LogOutput("request authz=<hidden>")
}
