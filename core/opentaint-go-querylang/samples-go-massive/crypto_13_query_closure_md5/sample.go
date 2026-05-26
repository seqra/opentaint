package util

import (
	"crypto/md5"
	"net/http"
)

var r *http.Request

// Positive_closure_md5: closure captures tainted query and hashes inside.
func Positive_closure_md5() {
	q := r.URL.Query().Get("q")
	fn := func() {
		_ = md5.Sum([]byte("salt:" + q))
	}
	fn()
}

// Negative_closure_unused: closure captures tainted but hashes a constant.
func Negative_closure_unused() {
	q := r.URL.Query().Get("q")
	_ = q
	fn := func() {
		_ = md5.Sum([]byte("static-data"))
	}
	fn()
}
