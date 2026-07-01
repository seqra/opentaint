package util

import (
	cryptorand "crypto/rand"
	mathrand "math/rand"
)

func Positive_math_rand_read() {
	_, _ = mathrand.Read(make([]byte, 16))
}

func Negative_crypto_rand_read() {
	_, _ = cryptorand.Read(make([]byte, 16))
}
