package util

import (
	"log"
	"net/http"
)

var r *http.Request

// Positive_form_logprint: FormValue passed directly to log.Print (newlines forge fake log lines).
func Positive_form_logprint() {
	v := r.FormValue("note")
	log.Print("note=" + v)
}

// Negative_form_const: form read but constant logged.
func Negative_form_const() {
	_ = r.FormValue("note")
	log.Print("note=<empty>")
}
