package util

import (
	"crypto/md5"
	"os"
)

// Positive_basic: tainted env hashed with weak MD5.
func Positive_basic() {
	v := os.Getenv("SECRET")
	_ = md5.Sum([]byte(v))
}

// Negative_const: env read but a constant is hashed.
func Negative_const() {
	_ = os.Getenv("SECRET")
	_ = md5.Sum([]byte("static-value"))
}
