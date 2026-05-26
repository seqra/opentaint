package util

import (
	"net/http"
	"strings"
)

var r *http.Request
var w http.ResponseWriter

// badEscape only strips angle brackets — incomplete sanitizer, treated as identity by the engine.
func badEscape(s string) string {
	s = strings.ReplaceAll(s, "<", "")
	return s
}

// Positive_bad_escape: form value goes through ineffective escape helper before being written.
func Positive_bad_escape() {
	v := r.FormValue("nickname")
	v = badEscape(v)
	w.Write([]byte("<span>" + v + "</span>"))
}

// Negative_const_helper: helper called on a constant; no taint reaches sink.
func Negative_const_helper() {
	_ = r.FormValue("nickname")
	v := badEscape("anon")
	w.Write([]byte("<span>" + v + "</span>"))
}
