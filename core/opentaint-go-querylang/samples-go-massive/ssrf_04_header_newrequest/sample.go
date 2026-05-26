package util

import (
	"net/http"
)

var r *http.Request

// Positive_headerurl: attacker-controlled X-Target-URL header used as request URL.
func Positive_headerurl() {
	u := r.Header.Get("X-Target-URL")
	req, _ := http.NewRequest("GET", u, nil)
	_ = req
}

// Negative_header_only_method: header used for METHOD only, URL constant.
func Negative_header_only_method() {
	m := r.Header.Get("X-Method")
	req, _ := http.NewRequest(m, "https://internal.svc/api", nil)
	_ = req
}
