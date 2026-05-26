package util

import (
	"encoding/xml"
	"net/http"
)

var r *http.Request

// Big is the deserialization target.
type Big struct {
	N string `xml:"n"`
}

// Positive_multiarg: confirm that arg 0 metavar $DATA matches the tainted byte slice.
func Positive_multiarg() {
	v := r.FormValue("payload")
	data := []byte(v)
	var target Big
	_ = xml.Unmarshal(data, &target)
}

// Negative_multiarg_const: tainted form value not embedded; constant decoded.
func Negative_multiarg_const() {
	_ = r.FormValue("payload")
	data := []byte(`<Big><n>safe</n></Big>`)
	var target Big
	_ = xml.Unmarshal(data, &target)
}
