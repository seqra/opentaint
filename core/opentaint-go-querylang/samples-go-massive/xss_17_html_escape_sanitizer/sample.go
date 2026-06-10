package util

import (
	"html"
	"net/http"
)

var r *http.Request
var w http.ResponseWriter

// Positive_unsanitized: tainted form value reaches w.Write with no escape.
func Positive_unsanitized() {
	v := r.FormValue("subject")
	w.Write([]byte("<h1>" + v + "</h1>"))
}

// Negative_sanitized: html.EscapeString is the canonical HTML-context sanitizer for reflected XSS.
func Negative_sanitized() {
	v := r.FormValue("subject")
	v = html.EscapeString(v)
	w.Write([]byte("<h1>" + v + "</h1>"))
}
