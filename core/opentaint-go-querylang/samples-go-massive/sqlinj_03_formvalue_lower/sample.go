package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Sink_DbQuery represents a real *sql.DB.Query call site (SQL injection sink).
func Sink_DbQuery(query string) { _ = query }

// Positive_lower: FormValue lowercased then concatenated into SQL.
func Positive_lower() {
	name := strings.ToLower(r.FormValue("name"))
	Sink_DbQuery("SELECT * FROM users WHERE name='" + name + "'")
}

// Negative_static: source not used; literal query.
func Negative_static() {
	_ = r.FormValue("name")
	Sink_DbQuery("SELECT * FROM users")
}
