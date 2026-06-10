package util

import (
	"crypto/md5"
	"net/http"
)

var r *http.Request

// normalizeKey is an allowlist-style sanitizer (treated as safe by the rule).
func normalizeKey(s string) string { _ = s; return "safe" }

// Positive_unsanitized: tainted form value hashed without sanitizer.
func Positive_unsanitized() {
	k := r.FormValue("k")
	_ = md5.Sum([]byte(k))
}

// Negative_sanitized: passed through normalizeKey allowlist before hashing.
func Negative_sanitized() {
	k := r.FormValue("k")
	k = normalizeKey(k)
	_ = md5.Sum([]byte(k))
}
