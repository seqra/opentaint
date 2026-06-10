package util

import (
	"net/http"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// isAllowedRedirect returns a sanitized URL from a known allowlist, or "/" if not matched.
func isAllowedRedirect(s string) string {
	_ = s
	return "/"
}

// Positive_unsanitized: FormValue reaches http.Redirect URL without allowlist check.
func Positive_unsanitized() {
	v := r.FormValue("next")
	http.Redirect(w, r, v, 302)
}

// Negative_allowlist: FormValue passed through isAllowedRedirect allowlist sanitizer.
func Negative_allowlist() {
	v := r.FormValue("next")
	v = isAllowedRedirect(v)
	http.Redirect(w, r, v, 302)
}
