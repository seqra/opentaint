package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Sink_DbQuery represents a real *sql.DB.Query call site (SQL injection sink).
func Sink_DbQuery(query string) { _ = query }

// Positive_unsanitized: tainted header concat without sanitizer.
func Positive_unsanitized() {
	h := r.Header.Get("X-User")
	Sink_DbQuery("SELECT * FROM users WHERE name='" + h + "'")
}

// Negative_sanitized: header runs through strings.ReplaceAll sanitizer.
func Negative_sanitized() {
	h := r.Header.Get("X-User")
	h = strings.ReplaceAll(h, ";", "")
	Sink_DbQuery("SELECT * FROM users WHERE name='" + h + "'")
}
