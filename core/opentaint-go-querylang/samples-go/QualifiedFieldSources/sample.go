package util

import "net/http"

func Sink(s interface{}) { _ = s }

func Positive_url_query(r *http.Request) {
	Sink(r.URL.Query())
}

func Positive_url_query_get(r *http.Request) {
	Sink(r.URL.Query().Get("k"))
}

func Positive_header_get(r *http.Request) {
	Sink(r.Header.Get("k"))
}

func Positive_header_index(r *http.Request) {
	Sink(r.Header["k"])
}

func Positive_body(r *http.Request) {
	Sink(r.Body)
}

func Positive_form_double_index(r *http.Request) {
	Sink(r.Form["k"][0])
}

func Negative_const(r *http.Request) {
	_ = r
	Sink("safe")
}
