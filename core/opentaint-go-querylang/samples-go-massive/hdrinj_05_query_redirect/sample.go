package util

import (
	"net/http"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// Positive_query_redirect: URL query value passed as URL to http.Redirect with status code 301.
func Positive_query_redirect() {
	d := r.URL.Query().Get("target")
	http.Redirect(w, r, d, 301)
}

// Negative_query_const: query read but constant target used.
func Negative_query_const() {
	_ = r.URL.Query().Get("target")
	http.Redirect(w, r, "/welcome", 301)
}
