package util

import (
	"encoding/xml"
	"fmt"
	"net/http"
)

var r *http.Request

// V is the deserialization target.
type V struct {
	A string `xml:"a"`
	B string `xml:"b"`
}

// Positive_variadic: tainted form value passed as one of several variadic
// fmt.Sprintf args building an XML payload.
func Positive_variadic() {
	tv := r.FormValue("inj")
	payload := fmt.Sprintf("<V><a>%s</a><b>%s</b></V>", "static", tv)
	var out V
	_ = xml.Unmarshal([]byte(payload), &out)
}

// Negative_variadic_unused: tainted read but not substituted into format.
func Negative_variadic_unused() {
	_ = r.FormValue("inj")
	payload := fmt.Sprintf("<V><a>%s</a><b>%s</b></V>", "x", "y")
	var out V
	_ = xml.Unmarshal([]byte(payload), &out)
}
