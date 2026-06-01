package util

import "net/http"

func Sink(s string) { _ = s }

func Positive_header_index(r *http.Request) {
	vals := r.Header["X-Test"]
	if len(vals) > 0 {
		Sink(vals[0])
	}
}

func Negative_const(r *http.Request) {
	_ = r
	Sink("safe")
}
