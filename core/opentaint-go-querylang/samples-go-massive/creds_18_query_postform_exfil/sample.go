package util

import (
	"net/http"
)

var r *http.Request

// Sink_PostFormBody represents http.PostForm outbound body data.
func Sink_PostFormBody(body string) { _ = body }

// Positive_query_postform: query token exfiltrated via outbound POST body.
func Positive_query_postform() {
	t := r.URL.Query().Get("token")
	Sink_PostFormBody("user_token=" + t)
}

// Negative_query_postform_const: query read but constant body posted.
func Negative_query_postform_const() {
	_ = r.URL.Query().Get("token")
	Sink_PostFormBody("user_token=anonymous")
}
