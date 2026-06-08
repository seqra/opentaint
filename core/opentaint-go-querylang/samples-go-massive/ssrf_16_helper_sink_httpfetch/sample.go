package util

import (
	"os"
)

// Sink_HttpFetch represents a third-party HTTP client call site such as
// resty.Get(url) or fasthttp.Get(nil, url) — same SSRF sink semantics as
// net/http.Get.
func Sink_HttpFetch(u string) { _ = u }

// Positive_helper_sink: env URL reaches third-party client sink.
func Positive_helper_sink() {
	u := os.Getenv("UPSTREAM")
	Sink_HttpFetch(u)
}

// Negative_helper_sink_const: env read but sink uses constant.
func Negative_helper_sink_const() {
	_ = os.Getenv("UPSTREAM")
	Sink_HttpFetch("https://internal.svc/api")
}
