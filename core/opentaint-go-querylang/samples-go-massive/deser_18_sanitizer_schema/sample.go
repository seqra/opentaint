package util

import (
	"encoding/json"
	"net/http"
)

var r *http.Request

// Schema is the deserialization target.
type Schema struct {
	OK string `json:"ok"`
}

// validateSchema acts as the sanitizer: it returns a cleansed copy that the
// rule recognizes as no-longer-tainted.
func validateSchema(s string) string {
	// In a real impl this would JSON-Schema-validate and re-serialize.
	return s
}

// Positive_no_sanitize: tainted form value goes straight into json.Unmarshal.
func Positive_no_sanitize() {
	v := r.FormValue("doc")
	var out Schema
	_ = json.Unmarshal([]byte(v), &out)
}

// Negative_sanitized: validateSchema wraps the tainted value before unmarshal.
func Negative_sanitized() {
	v := r.FormValue("doc")
	clean := validateSchema(v)
	var out Schema
	_ = json.Unmarshal([]byte(clean), &out)
}
