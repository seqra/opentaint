package util

import (
	"net/http"
)

var r *http.Request

// Sink_MongoFind represents a MongoDB Find() call site taking a raw JSON filter.
func Sink_MongoFind(filter string) { _ = filter }

// Positive_form_concat: FormValue concatenated into Mongo filter JSON.
func Positive_form_concat() {
	email := r.FormValue("email")
	f := `{"email":"` + email + `"}`
	Sink_MongoFind(f)
}

// Negative_form_const: FormValue read but constant filter sent.
func Negative_form_const() {
	_ = r.FormValue("email")
	Sink_MongoFind(`{"email":"nobody@example.com"}`)
}
