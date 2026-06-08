package util

import (
	"os"
	"strings"
)

// Sink_DbExec represents a real *sql.DB.Exec call site (SQL injection sink).
func Sink_DbExec(query string) { _ = query }

func sanitizeID(s string) string {
	return strings.ReplaceAll(s, "'", "")
}

// Positive_branch_one_clean: tainted only the unsanitized branch sinks.
func Positive_branch_one_clean() {
	l := os.Getenv("LIMIT")
	if len(l) > 5 {
		clean := sanitizeID(l)
		Sink_DbExec("DELETE FROM x LIMIT " + clean)
	} else {
		Sink_DbExec("DELETE FROM x LIMIT " + l)
	}
}

// Negative_branch_clean: tainted always sanitized before sink.
func Negative_branch_clean() {
	l := os.Getenv("LIMIT")
	clean := sanitizeID(l)
	Sink_DbExec("DELETE FROM x LIMIT " + clean)
}
