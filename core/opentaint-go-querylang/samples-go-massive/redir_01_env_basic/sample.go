package util

import (
	"net/http"
	"os"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// Positive_env_redirect: env directly used as redirect target (open redirect).
func Positive_env_redirect() {
	dest := os.Getenv("LOGIN_RETURN_URL")
	http.Redirect(w, r, dest, 302)
}

// Negative_env_const_redirect: env read but constant redirect target.
func Negative_env_const_redirect() {
	_ = os.Getenv("LOGIN_RETURN_URL")
	http.Redirect(w, r, "/account", 302)
}
