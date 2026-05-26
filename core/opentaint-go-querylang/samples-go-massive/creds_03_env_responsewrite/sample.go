package util

import (
	"os"
)

// Sink_ResponseWrite represents a real http.ResponseWriter.Write([]byte) call.
func Sink_ResponseWrite(body string) { _ = body }

// Positive_responsewrite: TOKEN concatenated into the response body.
func Positive_responsewrite() {
	t := os.Getenv("TOKEN")
	Sink_ResponseWrite("your token is: " + t)
}

// Negative_const: TOKEN read but the body is a constant.
func Negative_const() {
	_ = os.Getenv("TOKEN")
	Sink_ResponseWrite("ok")
}
