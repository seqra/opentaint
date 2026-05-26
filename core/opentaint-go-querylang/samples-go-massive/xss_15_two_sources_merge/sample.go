package util

import (
	"net/http"
	"os"
)

var r *http.Request
var w http.ResponseWriter

// Positive_merge: env and header concatenated; both are sources for this rule.
func Positive_merge() {
	a := os.Getenv("THEME")
	b := r.Header.Get("X-User")
	w.Write([]byte("<body class=\"" + a + "\"><h1>" + b + "</h1></body>"))
}

// Negative_merge_const: both sources read but constant body written.
func Negative_merge_const() {
	_ = os.Getenv("THEME")
	_ = r.Header.Get("X-User")
	w.Write([]byte("<body class=\"light\"><h1>anon</h1></body>"))
}
