package util

import (
	"net/http"
	"os"
)

// Positive_envdirect: env var read directly into http.Get URL.
func Positive_envdirect() {
	u := os.Getenv("TARGET_URL")
	_, _ = http.Get(u)
}

// Negative_const: env read but discarded; constant URL fetched.
func Negative_const() {
	_ = os.Getenv("TARGET_URL")
	_, _ = http.Get("https://example.com/")
}
