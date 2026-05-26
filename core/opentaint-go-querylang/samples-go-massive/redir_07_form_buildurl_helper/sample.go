package util

import (
	"net/http"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// buildRedirectURL constructs a redirect URL from a user-provided path.
func buildRedirectURL(p string) string {
	return "https://app.example.com" + p
}

// Positive_form_buildurl_redirect: FormValue passed through buildRedirectURL into http.Redirect.
func Positive_form_buildurl_redirect() {
	p := r.FormValue("path")
	url := buildRedirectURL(p)
	http.Redirect(w, r, url, 302)
}

// Negative_form_build_const: FormValue read but constant redirect target.
func Negative_form_build_const() {
	_ = r.FormValue("path")
	http.Redirect(w, r, "https://app.example.com/home", 302)
}
