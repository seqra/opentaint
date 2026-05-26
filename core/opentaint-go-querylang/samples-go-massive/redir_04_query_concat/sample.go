package util

import (
	"net/http"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// Positive_query_concat_redirect: query value concatenated into URL and redirected.
func Positive_query_concat_redirect() {
	dom := r.URL.Query().Get("domain")
	url := "https://" + dom + "/landing"
	http.Redirect(w, r, url, 302)
}

// Negative_query_concat_const: query unused; constant URL passed.
func Negative_query_concat_const() {
	_ = r.URL.Query().Get("domain")
	http.Redirect(w, r, "https://example.com/landing", 302)
}
