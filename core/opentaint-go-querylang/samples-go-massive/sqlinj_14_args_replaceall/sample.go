package util

import (
	"os"
	"strings"
)

// Sink_DbQueryRow represents a real *sql.DB.QueryRow call site (SQL injection sink).
func Sink_DbQueryRow(query string) { _ = query }

// Positive_replaceall: tainted os.Args transformed via ReplaceAll then concat.
func Positive_replaceall() {
	v := strings.ReplaceAll(os.Args[1], "_", "-")
	Sink_DbQueryRow("SELECT id FROM t WHERE slug='" + v + "'")
}

// Negative_replaceall_unused: source not propagated.
func Negative_replaceall_unused() {
	_ = strings.ReplaceAll(os.Args[1], "_", "-")
	Sink_DbQueryRow("SELECT id FROM t WHERE slug='static'")
}
