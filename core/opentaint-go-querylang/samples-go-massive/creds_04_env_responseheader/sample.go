package util

import (
	"os"
)

// Sink_ResponseHeader represents an http.Header.Set(key, value) call.
func Sink_ResponseHeader(key, value string) { _, _ = key, value }

// Positive_header_value: SECRET set as a response header value.
func Positive_header_value() {
	s := os.Getenv("SECRET")
	Sink_ResponseHeader("X-Debug-Secret", s)
}

// Negative_header_const_value: header set with constant value; env unused.
func Negative_header_const_value() {
	_ = os.Getenv("SECRET")
	Sink_ResponseHeader("X-Debug-Secret", "redacted")
}
