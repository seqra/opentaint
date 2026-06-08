package util

import (
	"encoding/json"
	"net/http"
)

var r *http.Request

// Session is the deserialization target.
type Session struct {
	ID string `json:"id"`
}

// Positive_cookie_header: Cookie value (read via Header.Get) decoded as JSON.
func Positive_cookie_header() {
	c := r.Header.Get("Cookie")
	var out Session
	_ = json.Unmarshal([]byte(c), &out)
}

// Negative_cookie_unused: cookie read but not used.
func Negative_cookie_unused() {
	_ = r.Header.Get("Cookie")
	var out Session
	_ = json.Unmarshal([]byte(`{"id":"safe"}`), &out)
}
