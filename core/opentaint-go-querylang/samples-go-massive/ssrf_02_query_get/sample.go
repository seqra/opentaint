package util

import (
	"net/http"
)

var r *http.Request

// Positive_querydirect: classic SSRF — attacker controls the entire URL via ?url=.
func Positive_querydirect() {
	u := r.URL.Query().Get("url")
	_, _ = http.Get(u)
}

// Negative_unused: query value read but unused.
func Negative_unused() {
	_ = r.URL.Query().Get("url")
	_, _ = http.Get("https://example.com/static")
}
