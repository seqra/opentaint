package util

import (
	"net/http"
	"strings"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// Positive_postform_trim_redirect: PostFormValue trimmed then used as redirect target.
func Positive_postform_trim_redirect() {
	v := r.PostFormValue("returnUrl")
	t := strings.TrimSpace(v)
	http.Redirect(w, r, t, 302)
}

// Negative_postform_const: PostFormValue read but constant target used.
func Negative_postform_const() {
	_ = r.PostFormValue("returnUrl")
	http.Redirect(w, r, "/profile", 302)
}
