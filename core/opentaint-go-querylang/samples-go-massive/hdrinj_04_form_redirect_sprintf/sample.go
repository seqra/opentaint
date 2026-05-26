package util

import (
	"fmt"
	"net/http"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// Positive_form_sprintf_redirect: FormValue formatted into URL passed to http.Redirect.
func Positive_form_sprintf_redirect() {
	v := r.FormValue("page")
	u := fmt.Sprintf("/p/%s", v)
	http.Redirect(w, r, u, 302)
}

// Negative_form_sprintf_const: FormValue read but constant Sprintf with no taint.
func Negative_form_sprintf_const() {
	_ = r.FormValue("page")
	u := fmt.Sprintf("/p/%s", "home")
	http.Redirect(w, r, u, 302)
}
