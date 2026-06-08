package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Sink_DbQueryRow represents a real *sql.DB.QueryRow call site (SQL injection sink).
func Sink_DbQueryRow(query string) { _ = query }

// Positive_upper: URL query value uppercased then concatenated.
func Positive_upper() {
	col := strings.ToUpper(r.URL.Query().Get("col"))
	Sink_DbQueryRow("SELECT " + col + " FROM accounts")
}

// Negative_drop: tainted result dropped.
func Negative_drop() {
	_ = strings.ToUpper(r.URL.Query().Get("col"))
	Sink_DbQueryRow("SELECT id FROM accounts")
}
