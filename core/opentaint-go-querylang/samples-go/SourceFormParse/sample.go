package util

import "net/http"

func Sink(s string) { _ = s }

func Positive_form_index(r *http.Request) {
	r.ParseForm()
	vals := r.Form["X-Test"]
	if len(vals) > 0 {
		Sink(vals[0])
	}
}

func Negative_const(r *http.Request) {
	_ = r
	Sink("safe")
}
