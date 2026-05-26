package util

import (
	"net/http"
	"strings"
)

var r *http.Request
var w http.ResponseWriter

// Positive_urlpath_write: tainted path segment reflected into body.
func Positive_urlpath_write() {
	p := r.URL.Query().Get("path")
	p = strings.TrimSpace(p)
	w.Write([]byte("You requested: " + p))
}

// Negative_urlpath_const: query read but constant path label written.
func Negative_urlpath_const() {
	_ = r.URL.Query().Get("path")
	w.Write([]byte("You requested: /"))
}
