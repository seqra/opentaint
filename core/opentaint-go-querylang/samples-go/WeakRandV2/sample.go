package weakrandv2

import (
	crand "crypto/rand"
	rand "math/rand/v2"
)

func Positive_v2_intn() {
	_ = rand.IntN(10)
}

func Positive_v2_float() {
	_ = rand.Float64()
}

func Negative_crypto_rand() {
	buf := make([]byte, 16)
	_, _ = crand.Read(buf)
}
