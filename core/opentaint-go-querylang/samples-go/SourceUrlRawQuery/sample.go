package util

import "net/http"

func Sink(s string) { _ = s }

func Positive_rawquery(r *http.Request) {
	s := r.URL.RawQuery
	Sink(s)
}

func Negative_const(r *http.Request) {
	_ = r
	s := "safe"
	Sink(s)
}
