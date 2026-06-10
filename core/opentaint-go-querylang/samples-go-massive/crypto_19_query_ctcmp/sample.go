package util

import (
	"crypto/subtle"
	"net/http"
)

var r *http.Request

// Positive_ctcmp_x: tainted query in arg 0 of ConstantTimeCompare.
func Positive_ctcmp_x() {
	q := r.URL.Query().Get("tok")
	_ = subtle.ConstantTimeCompare([]byte(q), []byte("expected-secret"))
}

// Negative_ctcmp_y: tainted in arg 1; focus is on $X so this is NOT a finding.
func Negative_ctcmp_y() {
	q := r.URL.Query().Get("tok")
	_ = subtle.ConstantTimeCompare([]byte("expected-secret"), []byte(q))
}
