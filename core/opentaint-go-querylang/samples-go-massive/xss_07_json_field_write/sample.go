package util

import (
	"encoding/json"
	"net/http"
)

// Comment models a stored comment record persisted from form input.
type Comment struct {
	Body string `json:"body"`
}

var r *http.Request
var w http.ResponseWriter

// Positive_stored: form body marshalled into JSON, then written to response (stored XSS pattern).
func Positive_stored() {
	body := r.FormValue("body")
	c := Comment{Body: body}
	b, _ := json.Marshal(c)
	w.Write(b)
}

// Negative_static_record: form read but a static record JSON written.
func Negative_static_record() {
	_ = r.FormValue("body")
	c := Comment{Body: "static"}
	b, _ := json.Marshal(c)
	w.Write(b)
}
