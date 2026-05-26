package util

import (
	"crypto/md5"
	"net/http"
)

var r *http.Request

// Positive_md5_write: tainted header fed into MD5 hash.Write.
func Positive_md5_write() {
	h := r.Header.Get("X-Token")
	m := md5.New()
	m.Write([]byte(h))
}

// Negative_md5_write_const: header read but a literal hashed.
func Negative_md5_write_const() {
	_ = r.Header.Get("X-Token")
	m := md5.New()
	m.Write([]byte("static-token"))
}
