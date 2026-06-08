package util

import (
	"os"
	"strings"
)

// Sink_DbQuery represents a real *sql.DB.Query call site (SQL injection sink).
func Sink_DbQuery(query string) { _ = query }

func normalize(s string) string {
	return strings.ToLower(strings.TrimSpace(s))
}

func wrap(s string) string {
	return "'" + s + "'"
}

// Positive_fullchain: env -> normalize -> wrap -> concat -> sink.
func Positive_fullchain() {
	q := wrap(normalize(os.Getenv("Q")))
	Sink_DbQuery("SELECT * FROM things WHERE name=" + q)
}

// Negative_fullchain_drop: pipeline runs but final result not used.
func Negative_fullchain_drop() {
	_ = wrap(normalize(os.Getenv("Q")))
	Sink_DbQuery("SELECT * FROM things")
}
