package util

import (
	"os"
)

// Sink_DbExec represents a real *sql.DB.Exec call site (SQL injection sink).
func Sink_DbExec(query string) { _ = query }

// Positive_direct: os.Args directly passed to sink.
func Positive_direct() {
	q := os.Args[1]
	Sink_DbExec(q)
}

// Negative_literal: tainted arg discarded; literal goes in.
func Negative_literal() {
	_ = os.Args[1]
	Sink_DbExec("DELETE FROM users WHERE id=1")
}
