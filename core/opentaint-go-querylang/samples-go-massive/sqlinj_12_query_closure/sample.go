package util

import (
	"net/http"
)

var r *http.Request

// Sink_DbQuery represents a real *sql.DB.Query call site (SQL injection sink).
func Sink_DbQuery(query string) { _ = query }

// Positive_closure: tainted captured by closure and used in sink.
func Positive_closure() {
	v := r.URL.Query().Get("v")
	fn := func() {
		Sink_DbQuery("SELECT * FROM t WHERE v='" + v + "'")
	}
	fn()
}

// Negative_closure_unused: closure created but captured value not used in sink.
func Negative_closure_unused() {
	v := r.URL.Query().Get("v")
	_ = v
	fn := func() {
		Sink_DbQuery("SELECT * FROM t")
	}
	fn()
}
