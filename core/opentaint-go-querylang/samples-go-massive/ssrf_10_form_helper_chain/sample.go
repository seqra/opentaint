package util

import (
	"net/http"
	"strings"
)

var r *http.Request

func buildURL(host string) string {
	host = strings.ToLower(host)
	return "https://" + host + "/v1/data"
}

func wrap(u string) string {
	return strings.TrimSpace(u)
}

// Positive_helper_chain: form -> buildURL -> wrap -> http.Get. Taint must
// propagate through both helper-function call boundaries.
func Positive_helper_chain() {
	h := r.FormValue("h")
	u := wrap(buildURL(h))
	_, _ = http.Get(u)
}

// Negative_helper_chain_drop: helpers run but their return value is discarded.
func Negative_helper_chain_drop() {
	h := r.FormValue("h")
	_ = wrap(buildURL(h))
	_, _ = http.Get("https://internal.svc/v1/data")
}
