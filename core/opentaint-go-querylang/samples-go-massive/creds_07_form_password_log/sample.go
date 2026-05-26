package util

import (
	"fmt"
	"net/http"
)

var r *http.Request

// Sink_LogOutput represents a log.Printf / log.Println style output sink.
func Sink_LogOutput(msg string) { _ = msg }

// Positive_form_password: password form value logged.
func Positive_form_password() {
	p := r.FormValue("password")
	Sink_LogOutput("user attempted login pass=" + p)
}

// Positive_form_password_sprintf: password formatted then logged.
func Positive_form_password_sprintf() {
	p := r.FormValue("password")
	Sink_LogOutput(fmt.Sprintf("login attempt pass=%q", p))
}

// Negative_form_password_const: password read but not logged.
func Negative_form_password_const() {
	_ = r.FormValue("password")
	Sink_LogOutput("login attempt")
}
