package util

import (
	"os"
)

// Sink_DbQuery represents a real *sql.DB.Query call site (SQL injection sink).
func Sink_DbQuery(query string) { _ = query }

// Positive_basic: env var concatenated into SQL.
func Positive_basic() {
	uid := os.Getenv("USER_ID")
	Sink_DbQuery("SELECT * FROM users WHERE id='" + uid + "'")
}

// Negative_const: env value discarded; constant goes in.
func Negative_const() {
	_ = os.Getenv("USER_ID")
	Sink_DbQuery("SELECT * FROM users WHERE id=1")
}
