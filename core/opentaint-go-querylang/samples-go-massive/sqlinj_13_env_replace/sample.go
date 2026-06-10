package util

import (
	"os"
	"strings"
)

// Sink_DbQuery represents a real *sql.DB.Query call site (SQL injection sink).
func Sink_DbQuery(query string) { _ = query }

// Positive_replace: tainted env transformed via strings.Replace then concat.
func Positive_replace() {
	f := strings.Replace(os.Getenv("FILTER"), "a", "b", -1)
	Sink_DbQuery("SELECT * FROM events WHERE filter='" + f + "'")
}

// Negative_replace_unused: result of Replace not used.
func Negative_replace_unused() {
	_ = strings.Replace(os.Getenv("FILTER"), "a", "b", -1)
	Sink_DbQuery("SELECT * FROM events")
}
