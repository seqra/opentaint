package util

import (
	"crypto/md5"
	"os"
	"strings"
)

// Positive_lower_md5: env → ToLower → md5.Sum.
func Positive_lower_md5() {
	v := os.Getenv("USERNAME")
	low := strings.ToLower(v)
	_ = md5.Sum([]byte(low))
}

// Negative_lower_const: env read but constant lowered and hashed.
func Negative_lower_const() {
	_ = os.Getenv("USERNAME")
	low := strings.ToLower("CONSTANT")
	_ = md5.Sum([]byte(low))
}
