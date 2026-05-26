package util

import (
	"net/http"
)

var r *http.Request
var w http.ResponseWriter

// Positive_cookie_write: cookie header value reflected into response body.
func Positive_cookie_write() {
	c := r.Header.Get("Cookie")
	w.Write([]byte("<p>last cookie=" + c + "</p>"))
}

// Negative_cookie_const: cookie read but constant body written.
func Negative_cookie_const() {
	_ = r.Header.Get("Cookie")
	w.Write([]byte("<p>welcome</p>"))
}
