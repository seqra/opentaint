package util

import (
	"fmt"
	"net/http"
)

var r *http.Request

// Sink_MongoFind represents a MongoDB Find() call site taking a raw JSON filter.
func Sink_MongoFind(filter string) { _ = filter }

// Positive_query_sprintf: URL query value into Mongo filter.
func Positive_query_sprintf() {
	q := r.URL.Query().Get("user")
	f := fmt.Sprintf(`{"user":"%s"}`, q)
	Sink_MongoFind(f)
}

// Negative_query_const: query read but constant filter sent.
func Negative_query_const() {
	_ = r.URL.Query().Get("user")
	Sink_MongoFind(`{"user":"guest"}`)
}
