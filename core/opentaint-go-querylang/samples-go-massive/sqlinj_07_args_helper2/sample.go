package util

import (
	"os"
	"strings"
)

// Sink_DbExec represents a real *sql.DB.Exec call site (SQL injection sink).
func Sink_DbExec(query string) { _ = query }

func step1(s string) string { return strings.ToUpper(s) }
func step2(s string) string { return strings.TrimSpace(s) }

// Positive_twohop: os.Args -> step1 -> step2 -> sink.
func Positive_twohop() {
	v := step2(step1(os.Args[1]))
	Sink_DbExec("UPDATE users SET role='" + v + "' WHERE id=1")
}

// Negative_twohop_dropped: chain runs but result ignored.
func Negative_twohop_dropped() {
	_ = step2(step1(os.Args[1]))
	Sink_DbExec("UPDATE users SET role='guest' WHERE id=1")
}
