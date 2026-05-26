package util

import (
	"fmt"
	"net/http"
)

var r *http.Request

// Positive_sprintf: form host substituted into Sprintf URL template, then fetched.
func Positive_sprintf() {
	host := r.FormValue("host")
	u := fmt.Sprintf("https://%s/api/v1/status", host)
	_, _ = http.Get(u)
}

// Negative_sprintf_unused: builds URL but fetches a constant elsewhere.
func Negative_sprintf_unused() {
	host := r.FormValue("host")
	_ = fmt.Sprintf("https://%s/api/v1/status", host)
	_, _ = http.Get("https://internal.svc/health")
}
