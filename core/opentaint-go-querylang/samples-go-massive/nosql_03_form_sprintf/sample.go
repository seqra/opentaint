package util

import (
	"fmt"
	"net/http"
)

var r *http.Request

// Sink_MongoFind represents a MongoDB Find() call site taking a raw JSON filter.
func Sink_MongoFind(filter string) { _ = filter }

// Positive_form_sprintf: FormValue interpolated into Mongo JSON filter.
func Positive_form_sprintf() {
	v := r.FormValue("name")
	f := fmt.Sprintf(`{"name":"%s"}`, v)
	Sink_MongoFind(f)
}

// Negative_form_sprintf_const: FormValue read but Sprintf with constant args.
func Negative_form_sprintf_const() {
	_ = r.FormValue("name")
	f := fmt.Sprintf(`{"name":"%s"}`, "default")
	Sink_MongoFind(f)
}
