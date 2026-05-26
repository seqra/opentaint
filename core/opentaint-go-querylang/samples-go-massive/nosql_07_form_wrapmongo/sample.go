package util

import (
	"net/http"
)

var r *http.Request

// Sink_MongoFind represents a MongoDB Find() call site taking a raw JSON filter.
func Sink_MongoFind(filter string) { _ = filter }

// wrapMongoFilter builds a Mongo $eq query from a user value.
func wrapMongoFilter(s string) string {
	return `{"username":{"$eq":"` + s + `"}}`
}

// Positive_form_wrapmongo: FormValue through wrapMongoFilter helper into sink.
func Positive_form_wrapmongo() {
	v := r.FormValue("uname")
	f := wrapMongoFilter(v)
	Sink_MongoFind(f)
}

// Negative_form_wrap_unused: FormValue read but constant filter used.
func Negative_form_wrap_unused() {
	_ = r.FormValue("uname")
	Sink_MongoFind(`{"username":{"$eq":"admin"}}`)
}
