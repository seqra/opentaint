package util

import (
	"math/rand"
	"os"
)

// Sink_RandSeed stands in for math/rand seeding (rand.New(rand.NewSource(seed))).
// Real callers pass an int64 seed derived from the string.
func Sink_RandSeed(s string) *rand.Rand {
	_ = s
	return rand.New(rand.NewSource(0))
}

// Positive_seed_from_env: tainted env used to seed predictable RNG.
func Positive_seed_from_env() {
	v := os.Getenv("SEED")
	_ = Sink_RandSeed(v)
}

// Negative_seed_const: env read but constant seed string used.
func Negative_seed_const() {
	_ = os.Getenv("SEED")
	_ = Sink_RandSeed("constant-seed")
}
