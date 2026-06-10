package util

import (
	"encoding/json"
	"net/http"
)

var r *http.Request

// User is the deserialization target.
type User struct {
	Name string `json:"name"`
}

// Positive_query: tainted URL query directly to json.Unmarshal.
func Positive_query() {
	q := r.URL.Query().Get("payload")
	var out User
	_ = json.Unmarshal([]byte(q), &out)
}

// Negative_query_unused: query read but unused; constant decoded.
func Negative_query_unused() {
	_ = r.URL.Query().Get("payload")
	var out User
	_ = json.Unmarshal([]byte(`{"name":"safe"}`), &out)
}
