package util

import (
	"crypto/md5"
	"os"
)

// Sink_AcceptHash absorbs the hash result so defer can wrap it.
func Sink_AcceptHash(h [16]byte) { _ = h }

// Positive_defer_md5: defer wraps md5.Sum call with tainted env value.
func Positive_defer_md5() {
	v := os.Getenv("PAYLOAD")
	defer Sink_AcceptHash(md5.Sum([]byte(v)))
}

// Negative_defer_md5_const: defer hashes a constant.
func Negative_defer_md5_const() {
	_ = os.Getenv("PAYLOAD")
	defer Sink_AcceptHash(md5.Sum([]byte("static")))
}
