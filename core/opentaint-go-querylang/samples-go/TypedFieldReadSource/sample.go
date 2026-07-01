package util

import "net/http"

func Sink(s string) { _ = s }

func Positive_typed_field_read_source(r *http.Request) {
	Sink(r.URL.Path)
}

func Negative_const(r *http.Request) {
	Sink("safe")
}
