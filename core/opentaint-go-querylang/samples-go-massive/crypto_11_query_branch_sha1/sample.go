package util

import (
	"crypto/sha1"
	"net/http"
)

var r *http.Request

// Positive_branch_taint: tainted on truthy branch reaches sha1.Write.
func Positive_branch_taint() {
	q := r.URL.Query().Get("q")
	var s string
	if len(q) > 0 {
		s = q
	} else {
		s = "default"
	}
	h := sha1.New()
	h.Write([]byte(s))
}

// Negative_branch_const: tainted only assigned to throwaway; const written.
func Negative_branch_const() {
	q := r.URL.Query().Get("q")
	_ = q
	h := sha1.New()
	h.Write([]byte("const-only"))
}
