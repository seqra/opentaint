package util

import (
	"crypto/md5"
	"fmt"
	"net/http"
)

var r *http.Request

// Positive_sprintf_md5: form value formatted via Sprintf then md5.Sum'd.
func Positive_sprintf_md5() {
	v := r.FormValue("token")
	seed := fmt.Sprintf("salt=%s|v=1", v)
	_ = md5.Sum([]byte(seed))
}

// Negative_sprintf_const: form read but constant template hashed.
func Negative_sprintf_const() {
	_ = r.FormValue("token")
	seed := fmt.Sprintf("salt=%s|v=1", "constant")
	_ = md5.Sum([]byte(seed))
}
