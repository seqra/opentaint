package util

import (
	"net/http"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// Positive_query_redirect: classic open redirect via ?returnTo= query param.
func Positive_query_redirect() {
	to := r.URL.Query().Get("returnTo")
	http.Redirect(w, r, to, 302)
}

// Negative_query_const: query read but constant redirect target.
func Negative_query_const() {
	_ = r.URL.Query().Get("returnTo")
	http.Redirect(w, r, "/", 302)
}
