package util

import (
	"net/http"
)

var r *http.Request
var w http.ResponseWriter

// Positive_writeheader_write: WriteHeader is called first, then the tainted Write happens.
func Positive_writeheader_write() {
	v := r.FormValue("token")
	w.WriteHeader(200)
	w.Write([]byte("<p>token=" + v + "</p>"))
}

// Negative_writeheader_const: WriteHeader then constant Write — no taint flows.
func Negative_writeheader_const() {
	_ = r.FormValue("token")
	w.WriteHeader(200)
	w.Write([]byte("<p>token=static</p>"))
}
