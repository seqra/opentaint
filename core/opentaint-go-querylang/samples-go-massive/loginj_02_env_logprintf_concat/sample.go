package util

import (
	"log"
	"os"
)

// Positive_env_concat_logprintf: env concatenated then logged via log.Printf %s.
func Positive_env_concat_logprintf() {
	r := os.Getenv("REQ_ID")
	msg := "request id=" + r
	log.Printf("%s", msg)
}

// Negative_env_unused: env read but unused; constant log line.
func Negative_env_unused() {
	_ = os.Getenv("REQ_ID")
	log.Printf("%s", "request id=anon")
}
