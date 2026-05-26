package util

import (
	"net/http"
	"regexp"
)

var r *http.Request

// Sink_DbQuery represents a real *sql.DB.Query call site (SQL injection sink).
func Sink_DbQuery(query string) { _ = query }

// Positive_noregex: tainted FormValue used unsanitized.
func Positive_noregex() {
	v := r.FormValue("v")
	Sink_DbQuery("SELECT * FROM t WHERE v='" + v + "'")
}

// Negative_regex_sanitized: regex sanitizer strips non-alnum chars.
func Negative_regex_sanitized() {
	v := r.FormValue("v")
	clean := regexp.MustCompile(`[^a-zA-Z0-9]`).ReplaceAllString(v, "")
	Sink_DbQuery("SELECT * FROM t WHERE v='" + clean + "'")
}
