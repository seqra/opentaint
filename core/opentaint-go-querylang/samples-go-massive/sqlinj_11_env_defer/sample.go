package util

import (
	"os"
)

// Sink_DbExec represents a real *sql.DB.Exec call site (SQL injection sink).
func Sink_DbExec(query string) { _ = query }

// Positive_defer: defer wraps the sink with tainted env.
func Positive_defer() {
	c := os.Getenv("CLEANUP")
	defer Sink_DbExec("DELETE FROM tmp WHERE tag='" + c + "'")
}

// Negative_defer_const: defer sinks but does not use tainted value.
func Negative_defer_const() {
	_ = os.Getenv("CLEANUP")
	defer Sink_DbExec("DELETE FROM tmp WHERE tag='default'")
}
