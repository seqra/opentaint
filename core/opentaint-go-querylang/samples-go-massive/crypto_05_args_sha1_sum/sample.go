package util

import (
	"crypto/sha1"
	"os"
)

// Positive_args_sha1: tainted CLI arg sha1.Sum'd.
func Positive_args_sha1() {
	v := os.Args[1]
	_ = sha1.Sum([]byte(v))
}

// Negative_args_const: arg read but constant hashed.
func Negative_args_const() {
	_ = os.Args[1]
	_ = sha1.Sum([]byte("constant-bytes"))
}
