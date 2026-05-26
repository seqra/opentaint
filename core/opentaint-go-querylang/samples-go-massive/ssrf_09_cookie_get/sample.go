package util

import (
	"net/http"
)

var r *http.Request

// Positive_cookie_url: read raw Cookie header (string is attacker-controlled),
// substring used as fetch URL.
func Positive_cookie_url() {
	c := r.Header.Get("Cookie")
	// pretend we parse a cookie value; the parsed substring is still tainted.
	u := "https://" + c + "/cb"
	_, _ = http.Get(u)
}

// Negative_cookie_logged: cookie read but only logged into local var; fetch
// uses a constant URL.
func Negative_cookie_logged() {
	_ = r.Header.Get("Cookie")
	_, _ = http.Get("https://internal.svc/cb")
}
