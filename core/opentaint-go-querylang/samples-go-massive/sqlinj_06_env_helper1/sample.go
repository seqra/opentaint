package util

import (
	"os"
	"strings"
)

// Sink_DbQuery represents a real *sql.DB.Query call site (SQL injection sink).
func Sink_DbQuery(query string) { _ = query }

func transform(s string) string {
	return strings.ToLower(s)
}

// Positive_helper1: env tainted, transformed via 1-hop helper, then concatenated.
func Positive_helper1() {
	ord := transform(os.Getenv("ORDER_BY"))
	Sink_DbQuery("SELECT * FROM products ORDER BY " + ord)
}

// Negative_helperdrop: helper called but result not used.
func Negative_helperdrop() {
	_ = transform(os.Getenv("ORDER_BY"))
	Sink_DbQuery("SELECT * FROM products ORDER BY id")
}
