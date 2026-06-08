package util

import (
	"net/http"
	"strings"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// wrapLocation prefixes /go/ before the supplied path.
func wrapLocation(s string) string {
	return "/go/" + strings.TrimSpace(s)
}

// Positive_header_helper_redirect: X-Forwarded header through wrapLocation helper into http.Redirect URL.
func Positive_header_helper_redirect() {
	h := r.Header.Get("X-Forwarded-Path")
	u := wrapLocation(h)
	http.Redirect(w, r, u, 302)
}

// Negative_header_unused: header read but constant URL passed to Redirect.
func Negative_header_unused() {
	_ = r.Header.Get("X-Forwarded-Path")
	http.Redirect(w, r, "/go/home", 302)
}
