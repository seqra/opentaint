package util

import (
	"net/http"
	"os"
)

var r *http.Request

// Positive_form: form value flows directly into os.ReadFile.
func Positive_form() {
	name := r.FormValue("doc")
	b, _ := os.ReadFile("/srv/docs/" + name)
	_ = b
}

// Positive_form_direct: form value used as the full path with no prefix.
func Positive_form_direct() {
	name := r.FormValue("doc")
	b, _ := os.ReadFile(name)
	_ = b
}

// Negative_const: form read but constant path is used.
func Negative_const() {
	_ = r.FormValue("doc")
	b, _ := os.ReadFile("/srv/docs/index.txt")
	_ = b
}
