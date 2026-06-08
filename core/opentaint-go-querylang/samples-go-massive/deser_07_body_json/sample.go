package util

import (
	"encoding/json"
	"io/ioutil"
	"net/http"
)

var r *http.Request

// Payload is the deserialization target.
type Payload struct {
	Name string `json:"name"`
}

// Positive_body: read request body bytes and json.Unmarshal them.
func Positive_body() {
	b, _ := ioutil.ReadAll(r.Body)
	var out Payload
	_ = json.Unmarshal(b, &out)
}

// Negative_body_unused: body read but discarded; constant decoded.
func Negative_body_unused() {
	_, _ = ioutil.ReadAll(r.Body)
	var out Payload
	_ = json.Unmarshal([]byte(`{"name":"safe"}`), &out)
}
