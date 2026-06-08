package util

import (
	"net/http"
)

var r *http.Request

// Sink_DbQuery represents a real *sql.DB.Query call site (SQL injection sink).
func Sink_DbQuery(query string) { _ = query }

// Positive_for: tainted FormValue used per-iteration inside for-range loop.
func Positive_for() {
	rows := []string{"a", "b", "c"}
	uname := r.FormValue("uname")
	for _, x := range rows {
		Sink_DbQuery("SELECT " + x + " FROM users WHERE name='" + uname + "'")
	}
}

// Negative_for_const: source ignored per-iter.
func Negative_for_const() {
	rows := []string{"a", "b", "c"}
	_ = r.FormValue("uname")
	for _, x := range rows {
		Sink_DbQuery("SELECT " + x + " FROM users")
	}
}
