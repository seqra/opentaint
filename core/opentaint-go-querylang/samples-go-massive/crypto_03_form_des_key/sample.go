package util

import (
	"crypto/des"
	"net/http"
)

var r *http.Request

// Positive_des_key: tainted form value becomes the DES cipher key.
func Positive_des_key() {
	k := r.FormValue("key")
	_, _ = des.NewCipher([]byte(k))
}

// Negative_des_const: form read but constant key used.
func Negative_des_const() {
	_ = r.FormValue("key")
	_, _ = des.NewCipher([]byte("abcdefgh"))
}
