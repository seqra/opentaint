package util

import (
	"net/http"
	"os"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// Positive_env_redirect: env passed directly as URL into http.Redirect (header injection via Location).
func Positive_env_redirect() {
	u := os.Getenv("NEXT_URL")
	http.Redirect(w, r, u, 302)
}

// Negative_env_const: env read but constant Location.
func Negative_env_const() {
	_ = os.Getenv("NEXT_URL")
	http.Redirect(w, r, "/home", 302)
}
