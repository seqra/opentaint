package util

import (
	"net/http"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// Positive_form_redirect: FormValue passed directly as URL into http.Redirect.
func Positive_form_redirect() {
	dst := r.FormValue("dest")
	http.Redirect(w, r, dst, 302)
}

// Negative_form_const: FormValue read but unused; constant URL.
func Negative_form_const() {
	_ = r.FormValue("dest")
	http.Redirect(w, r, "/dashboard", 302)
}
