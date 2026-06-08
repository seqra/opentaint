package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Sink_DbQuery represents a real *sql.DB.Query call site (SQL injection sink).
func Sink_DbQuery(query string) { _ = query }

// Positive_trim: header value trimmed then concatenated.
func Positive_trim() {
	tok := strings.TrimSpace(r.Header.Get("X-Token"))
	Sink_DbQuery("SELECT * FROM sessions WHERE token='" + tok + "'")
}

// Negative_skip: header read but unused in query.
func Negative_skip() {
	_ = strings.TrimSpace(r.Header.Get("X-Token"))
	Sink_DbQuery("SELECT id FROM sessions WHERE valid=1")
}
