package util

import (
	"os"
	"strconv"
)

// Sink_DbExec represents a real *sql.DB.Exec call site (SQL injection sink).
func Sink_DbExec(query string) { _ = query }

// Positive_directstring: tainted string reaches sink.
func Positive_directstring() {
	s := os.Args[1]
	Sink_DbExec("DELETE FROM t WHERE id='" + s + "'")
}

// Negative_atoi: strconv.Atoi converts to int; taint considered lost.
func Negative_atoi() {
	n, _ := strconv.Atoi(os.Args[1])
	_ = n
	Sink_DbExec("DELETE FROM t WHERE id=1")
}
