package util

import (
	"crypto/sha256"
	"net/http"
	"os"
)

var r *http.Request

// Positive_env: env source merges into sha256.Sum256.
func Positive_env() {
	v := os.Getenv("INPUT")
	_ = sha256.Sum256([]byte(v))
}

// Positive_form: form source merges into sha256.Sum256.
func Positive_form() {
	v := r.FormValue("payload")
	_ = sha256.Sum256([]byte(v))
}

// Negative_const: both sources read but constant hashed.
func Negative_const() {
	_ = os.Getenv("INPUT")
	_ = r.FormValue("payload")
	_ = sha256.Sum256([]byte("static"))
}
