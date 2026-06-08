package util

import (
	"net/http"
	"os"
	"strings"
)

var r *http.Request

// Positive_trimprefix: URL query value stripped of a prefix; still tainted.
func Positive_trimprefix() {
	raw := r.URL.Query().Get("path")
	name := strings.TrimPrefix(raw, "/files/")
	b, _ := os.ReadFile("/srv/" + name)
	_ = b
}

// Negative_const: query read but a constant path is used.
func Negative_const() {
	_ = r.URL.Query().Get("path")
	b, _ := os.ReadFile("/srv/index.html")
	_ = b
}
