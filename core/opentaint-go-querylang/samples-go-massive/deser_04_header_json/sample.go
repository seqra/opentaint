package util

import (
	"encoding/json"
	"net/http"
)

var r *http.Request

// Cfg is the deserialization target.
type Cfg struct {
	Mode string `json:"mode"`
}

// Positive_header_direct: header value parsed as JSON without checks.
func Positive_header_direct() {
	h := r.Header.Get("X-Config")
	var out Cfg
	_ = json.Unmarshal([]byte(h), &out)
}

// Positive_header_concat: header concatenated into JSON body.
func Positive_header_concat() {
	h := r.Header.Get("X-Mode")
	body := `{"mode":"` + h + `"}`
	var out Cfg
	_ = json.Unmarshal([]byte(body), &out)
}

// Negative_header_logged: header read for logging only.
func Negative_header_logged() {
	_ = r.Header.Get("X-Config")
	var out Cfg
	_ = json.Unmarshal([]byte(`{"mode":"safe"}`), &out)
}
