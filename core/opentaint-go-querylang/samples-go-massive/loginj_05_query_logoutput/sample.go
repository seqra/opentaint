package util

import (
	"log"
	"net/http"
)

var (
	r *http.Request
	l *log.Logger
)

// Positive_query_logoutput_msg: URL query value passed to log.Output as $MSG.
func Positive_query_logoutput_msg() {
	q := r.URL.Query().Get("trace")
	_ = l.Output(2, "trace="+q)
}

// Negative_query_logoutput_const: query read but $MSG arg is constant.
func Negative_query_logoutput_const() {
	_ = r.URL.Query().Get("trace")
	_ = l.Output(2, "trace=<none>")
}
