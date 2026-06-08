package util

import (
	"os"
)

// Sink_DbExec represents a real *sql.DB.Exec call site (SQL injection sink).
func Sink_DbExec(query string) { _ = query }

// Positive_switch: switch dispatch but tainted value sinks in case branches.
func Positive_switch() {
	a := os.Args[1]
	switch a {
	case "create":
		Sink_DbExec("INSERT INTO actions VALUES ('" + a + "')")
	default:
		Sink_DbExec("INSERT INTO actions VALUES ('" + a + "')")
	}
}

// Negative_switch_const: tainted matched but never used in query.
func Negative_switch_const() {
	a := os.Args[1]
	switch a {
	case "create":
		Sink_DbExec("INSERT INTO actions VALUES ('create')")
	default:
		Sink_DbExec("INSERT INTO actions VALUES ('unknown')")
	}
}
