package util

import (
	"net/http"
	"os"
	"strings"
)

var r *http.Request

// Positive_loop: comma-separated user input split into slice and each entry deleted.
func Positive_loop() {
	raw := r.FormValue("files")
	parts := strings.Split(raw, ",")
	for _, name := range parts {
		_ = os.Remove("/var/cache/" + name)
	}
}

// Negative_const_loop: form read but a fixed slice is iterated.
func Negative_const_loop() {
	_ = r.FormValue("files")
	for _, name := range []string{"a.tmp", "b.tmp"} {
		_ = os.Remove("/var/cache/" + name)
	}
}
