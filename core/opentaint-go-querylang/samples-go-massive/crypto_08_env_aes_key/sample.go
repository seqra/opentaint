package util

import (
	"crypto/aes"
	"os"
)

// Positive_aes_env_key: tainted env value used as AES key bytes.
func Positive_aes_env_key() {
	k := os.Getenv("AES_KEY")
	_, _ = aes.NewCipher([]byte(k))
}

// Negative_aes_const_key: env read but constant key used.
func Negative_aes_const_key() {
	_ = os.Getenv("AES_KEY")
	_, _ = aes.NewCipher([]byte("0123456789abcdef"))
}
