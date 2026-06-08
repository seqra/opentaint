package util

import (
	"fmt"
	"log"
	"net/http"
)

var (
	r *http.Request
	l *log.Logger
)

// Positive_query_sprintf_logoutput: URL query value formatted then passed to log.Output $MSG.
func Positive_query_sprintf_logoutput() {
	q := r.URL.Query().Get("session")
	m := fmt.Sprintf("session=%s", q)
	_ = l.Output(2, m)
}

// Negative_query_sprintf_const: $MSG is a constant string.
func Negative_query_sprintf_const() {
	_ = r.URL.Query().Get("session")
	_ = l.Output(2, "session=<empty>")
}
