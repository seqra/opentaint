package util

import (
	"fmt"
	"net/http"
	"os"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// Positive_env_sprintf_redirect: env interpolated into URL via Sprintf and passed to Redirect.
func Positive_env_sprintf_redirect() {
	host := os.Getenv("FRONTEND_HOST")
	url := fmt.Sprintf("https://%s/dashboard", host)
	http.Redirect(w, r, url, 302)
}

// Negative_env_sprintf_const: env unused; Sprintf with constant host.
func Negative_env_sprintf_const() {
	_ = os.Getenv("FRONTEND_HOST")
	url := fmt.Sprintf("https://%s/dashboard", "example.com")
	http.Redirect(w, r, url, 302)
}
