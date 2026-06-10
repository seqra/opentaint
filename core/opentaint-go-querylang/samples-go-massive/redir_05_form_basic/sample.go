package util

import (
	"net/http"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// Positive_form_redirect: classic POST-login form redirect target attacker-controlled.
func Positive_form_redirect() {
	target := r.FormValue("next")
	http.Redirect(w, r, target, 303)
}

// Negative_form_const: FormValue read but constant target used.
func Negative_form_const() {
	_ = r.FormValue("next")
	http.Redirect(w, r, "/dashboard", 303)
}
