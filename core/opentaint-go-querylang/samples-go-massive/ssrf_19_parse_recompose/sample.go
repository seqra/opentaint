package util

import (
	"net/http"
	"net/url"
)

var r *http.Request

// Positive_parse_recompose: developer believes url.Parse "validates" the URL,
// then recomposes via .String(). Host is still attacker-controlled — taint
// flows through net/url and the result feeds http.Get.
func Positive_parse_recompose() {
	raw := r.URL.Query().Get("u")
	parsed, err := url.Parse(raw)
	if err == nil {
		_, _ = http.Get(parsed.String())
	}
}

// Negative_parse_only: parses tainted URL but does not use it in a fetch.
func Negative_parse_only() {
	raw := r.URL.Query().Get("u")
	parsed, _ := url.Parse(raw)
	_ = parsed
	_, _ = http.Get("https://internal.svc/static")
}
