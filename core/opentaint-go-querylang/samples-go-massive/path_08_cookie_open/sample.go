package util

import (
	"net/http"
	"os"
	"strings"
)

var r *http.Request

// Positive_cookie: cookie header parsed for session id, used as part of file path.
func Positive_cookie() {
	cookie := r.Header.Get("Cookie")
	// Take the cookie value after the first '=' as a session name.
	idx := strings.Index(cookie, "=")
	name := cookie[idx+1:]
	f, _ := os.Open("/var/sessions/" + name + ".bin")
	_ = f
}

// Negative_const: cookie read but a constant path opened.
func Negative_const() {
	_ = r.Header.Get("Cookie")
	f, _ := os.Open("/var/sessions/anon.bin")
	_ = f
}
