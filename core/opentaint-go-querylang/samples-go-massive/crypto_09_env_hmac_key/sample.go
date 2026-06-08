package util

import (
	"crypto/hmac"
	"crypto/sha1"
	"os"
)

// Positive_hmac_key: tainted env becomes HMAC key.
func Positive_hmac_key() {
	k := os.Getenv("HMAC_KEY")
	_ = hmac.New(sha1.New, []byte(k))
}

// Negative_hmac_const_key: env read but constant key used.
func Negative_hmac_const_key() {
	_ = os.Getenv("HMAC_KEY")
	_ = hmac.New(sha1.New, []byte("static-hmac-key"))
}
