package util

import (
	"crypto/md5"
	"encoding/hex"
	"os"
)

// Positive_hex_concat: env hex-encoded then concatenated and md5.Sum'd.
func Positive_hex_concat() {
	v := os.Getenv("INPUT")
	enc := hex.EncodeToString([]byte(v))
	combined := "prefix:" + enc
	_ = md5.Sum([]byte(combined))
}

// Negative_hex_const: hex of a literal hashed; env unused.
func Negative_hex_const() {
	_ = os.Getenv("INPUT")
	enc := hex.EncodeToString([]byte("safe-data"))
	_ = md5.Sum([]byte(enc))
}
