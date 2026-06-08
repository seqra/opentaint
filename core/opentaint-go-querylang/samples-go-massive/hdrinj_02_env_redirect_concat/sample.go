package util

import (
	"net/http"
	"os"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// Positive_env_concat_redirect: env concatenated into URL passed to http.Redirect.
func Positive_env_concat_redirect() {
	p := os.Getenv("PATH_NEXT")
	u := "/app" + p
	http.Redirect(w, r, u, 302)
}

// Negative_env_const_path: env read but constant path used.
func Negative_env_const_path() {
	_ = os.Getenv("PATH_NEXT")
	http.Redirect(w, r, "/app/index", 302)
}
