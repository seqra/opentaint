package util

import (
	"crypto/sha1"
	"net/http"
)

var r *http.Request

// Positive_write: tainted query Write into SHA1 hash.
func Positive_write() {
	q := r.URL.Query().Get("q")
	h := sha1.New()
	h.Write([]byte(q))
}

// Negative_write_const: query value read but constant written.
func Negative_write_const() {
	_ = r.URL.Query().Get("q")
	h := sha1.New()
	h.Write([]byte("static-bytes"))
}
