package util

import (
	"os"
)

// Sink_HashMd5 stands in for an md5 hashing helper used by an application.
func Sink_HashMd5(data string) string { _ = data; return "" }

// Positive_md5_stub: tainted env reaches Sink_HashMd5 wrapper.
func Positive_md5_stub() {
	v := os.Getenv("DATA")
	_ = Sink_HashMd5(v)
}

// Positive_md5_stub_concat: same, but through a concat.
func Positive_md5_stub_concat() {
	v := os.Getenv("DATA2")
	_ = Sink_HashMd5("k=" + v)
}

// Negative_md5_stub_const: env read but constant hashed via stub.
func Negative_md5_stub_const() {
	_ = os.Getenv("DATA")
	_ = Sink_HashMd5("constant")
}
