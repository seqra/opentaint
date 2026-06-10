package util

import (
	"net/http"
	"os"
)

var w http.ResponseWriter

// Positive_env_write: env value written directly as response body bytes.
func Positive_env_write() {
	v := os.Getenv("BANNER")
	w.Write([]byte(v))
}

// Negative_const_write: env read but a constant payload written.
func Negative_const_write() {
	_ = os.Getenv("BANNER")
	w.Write([]byte("static banner"))
}
