package util

import (
	"net/http"
)

var r *http.Request
var w http.ResponseWriter

// Positive_query_writestring: query parameter reflected via WriteString.
func Positive_query_writestring() {
	q := r.URL.Query().Get("name")
	w.WriteString("<h1>Hello " + q + "</h1>")
}

// Negative_no_query: query not read; safe constant string written.
func Negative_no_query() {
	w.WriteString("<h1>Hello world</h1>")
}
