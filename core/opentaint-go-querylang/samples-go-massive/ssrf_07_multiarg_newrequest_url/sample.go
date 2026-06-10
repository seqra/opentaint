package util

import (
	"net/http"
)

var r *http.Request

// Positive_url_arg: form value flows into the URL argument (arg 2).
func Positive_url_arg() {
	u := r.FormValue("dest")
	req, _ := http.NewRequest("GET", u, nil)
	_ = req
}

// Negative_method_arg: form value flows into method (arg 1) only —
// focus-metavariable on $URL means this is NOT a finding.
func Negative_method_arg() {
	m := r.FormValue("method")
	req, _ := http.NewRequest(m, "https://internal.svc/api", nil)
	_ = req
}
