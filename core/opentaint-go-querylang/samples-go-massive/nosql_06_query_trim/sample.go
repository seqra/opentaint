package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Sink_MongoFind represents a MongoDB Find() call site taking a raw JSON filter.
func Sink_MongoFind(filter string) { _ = filter }

// Positive_query_trim_concat: URL query trimmed then concatenated into Mongo filter.
func Positive_query_trim_concat() {
	q := r.URL.Query().Get("ref")
	t := strings.TrimSpace(q)
	Sink_MongoFind(`{"ref":"` + t + `"}`)
}

// Negative_query_trim_const: query read but constant filter sent.
func Negative_query_trim_const() {
	_ = r.URL.Query().Get("ref")
	Sink_MongoFind(`{"ref":"none"}`)
}
