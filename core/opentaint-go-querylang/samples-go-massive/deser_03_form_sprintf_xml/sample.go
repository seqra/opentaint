package util

import (
	"encoding/xml"
	"fmt"
	"net/http"
)

var r *http.Request

// Doc is the deserialization target.
type Doc struct {
	Body string `xml:"body"`
}

// Positive_sprintf: tainted form value embedded via fmt.Sprintf into XML body.
func Positive_sprintf() {
	v := r.FormValue("body")
	payload := fmt.Sprintf("<Doc><body>%s</body></Doc>", v)
	var out Doc
	_ = xml.Unmarshal([]byte(payload), &out)
}

// Negative_sprintf_const: fmt.Sprintf used but no tainted input substituted.
func Negative_sprintf_const() {
	_ = r.FormValue("body")
	payload := fmt.Sprintf("<Doc><body>%s</body></Doc>", "static")
	var out Doc
	_ = xml.Unmarshal([]byte(payload), &out)
}
