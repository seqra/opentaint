package util

import (
	"net/http"
	"os"
	"path/filepath"
)

var r *http.Request

// Positive_join_escape: filepath.Join does NOT block "../" traversal, only normalizes.
func Positive_join_escape() {
	name := r.URL.Query().Get("file")
	p := filepath.Join("/var/data", name)
	f, _ := os.OpenFile(p, os.O_RDONLY, 0)
	_ = f
}

// Negative_const: query read but constant path opened.
func Negative_const() {
	_ = r.URL.Query().Get("file")
	f, _ := os.OpenFile("/var/data/static.txt", os.O_RDONLY, 0)
	_ = f
}
