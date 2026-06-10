package util

import (
	"io"
	"net/http"
)

var r *http.Request
var w http.ResponseWriter

// Positive_header_iowrite: header value sent through io.WriteString.
func Positive_header_iowrite() {
	h := r.Header.Get("X-Greeting")
	io.WriteString(w, "<p>"+h+"</p>")
}

// Negative_const_iowrite: header read but constant string written.
func Negative_const_iowrite() {
	_ = r.Header.Get("X-Greeting")
	io.WriteString(w, "<p>hello</p>")
}
