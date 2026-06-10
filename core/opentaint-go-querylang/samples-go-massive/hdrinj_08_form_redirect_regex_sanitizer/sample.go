package util

import (
	"net/http"
	"regexp"
)

var (
	w http.ResponseWriter
	r *http.Request
)

// Positive_unsanitized: FormValue reaches http.Redirect URL with no allowlist.
func Positive_unsanitized() {
	v := r.FormValue("next")
	http.Redirect(w, r, v, 302)
}

// Negative_regex_allowlist: regex strips all non-path chars before redirect.
func Negative_regex_allowlist() {
	v := r.FormValue("next")
	safe := regexp.MustCompile(`[^a-zA-Z0-9/_-]`).ReplaceAllString(v, "")
	http.Redirect(w, r, safe, 302)
}
