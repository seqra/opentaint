package importqualified

import (
	crand "crypto/rand"
	"math/big"
	mrand "math/rand"
)

func Positive_math_rand() {
	_ = mrand.Int()
}

func Negative_crypto_rand() {
	_, _ = crand.Int(crand.Reader, big.NewInt(100))
}
