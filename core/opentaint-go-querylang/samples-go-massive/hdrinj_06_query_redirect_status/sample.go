package util

import (
	"net/http"
	"strings"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// Positive_query_lower_redirect: query value lowercased then passed as Location into http.Redirect (status 307).
func Positive_query_lower_redirect() {
	q := r.URL.Query().Get("loc")
	lo := strings.ToLower(q)
	http.Redirect(w, r, lo, 307)
}

// Negative_const_status: query read but constant Location.
func Negative_const_status() {
	_ = r.URL.Query().Get("loc")
	http.Redirect(w, r, "/home", 307)
}
