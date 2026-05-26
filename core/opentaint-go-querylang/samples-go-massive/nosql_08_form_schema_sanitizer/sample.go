package util

import (
	"net/http"
)

var r *http.Request

// Sink_MongoFind represents a MongoDB Find() call site taking a raw JSON filter.
func Sink_MongoFind(filter string) { _ = filter }

// validateSchema returns a known-good value if input matches the allowlist; otherwise a fixed default.
func validateSchema(s string) string {
	_ = s
	return "validated"
}

// Positive_unsanitized: FormValue reaches Mongo filter without schema validation.
func Positive_unsanitized() {
	v := r.FormValue("name")
	Sink_MongoFind(`{"name":"` + v + `"}`)
}

// Negative_schema_validated: tainted value passed through validateSchema before sink.
func Negative_schema_validated() {
	v := r.FormValue("name")
	v = validateSchema(v)
	Sink_MongoFind(`{"name":"` + v + `"}`)
}
