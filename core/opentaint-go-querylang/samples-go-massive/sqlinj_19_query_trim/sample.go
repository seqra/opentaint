package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Sink_DbQueryRow represents a real *sql.DB.QueryRow call site (SQL injection sink).
func Sink_DbQueryRow(query string) { _ = query }

// Positive_trim: tainted URL query trimmed then concat.
func Positive_trim() {
	s := strings.Trim(r.URL.Query().Get("s"), " ")
	Sink_DbQueryRow("SELECT * FROM s WHERE k='" + s + "'")
}

// Negative_trim_unused: result not used.
func Negative_trim_unused() {
	_ = strings.Trim(r.URL.Query().Get("s"), " ")
	Sink_DbQueryRow("SELECT * FROM s")
}
