package util

import (
	"encoding/json"
	"net/http"
)

var r *http.Request

// Box is the deserialization target.
type Box struct {
	V string `json:"v"`
}

// Positive_closure: closure captures tainted query and runs json.Unmarshal inside.
func Positive_closure() {
	q := r.URL.Query().Get("data")
	fn := func() {
		var out Box
		_ = json.Unmarshal([]byte(q), &out)
	}
	fn()
}

// Negative_closure_unused: closure captures but does not use tainted value.
func Negative_closure_unused() {
	q := r.URL.Query().Get("data")
	_ = q
	fn := func() {
		var out Box
		_ = json.Unmarshal([]byte(`{"v":"safe"}`), &out)
	}
	fn()
}
