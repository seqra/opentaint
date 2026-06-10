package util

import (
	"os"
)

// Sink_DbQuery represents a real *sql.DB.Query call site (SQL injection sink).
func Sink_DbQuery(query string) { _ = query }

// Positive_branchsink: only the true branch sinks tainted value.
func Positive_branchsink() {
	m := os.Getenv("MODE")
	if len(m) > 0 {
		Sink_DbQuery("SELECT * FROM logs WHERE mode='" + m + "'")
	} else {
		Sink_DbQuery("SELECT * FROM logs")
	}
}

// Negative_otherbranch: tainted only in non-sinking branch.
func Negative_otherbranch() {
	m := os.Getenv("MODE")
	if len(m) > 0 {
		_ = m
		Sink_DbQuery("SELECT * FROM logs")
	} else {
		Sink_DbQuery("SELECT * FROM logs WHERE mode='default'")
	}
}
