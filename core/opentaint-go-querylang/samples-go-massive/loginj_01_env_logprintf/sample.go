package util

import (
	"log"
	"os"
)

// Positive_env_logprintf: env directly interpolated into log.Printf (newline injection risk).
func Positive_env_logprintf() {
	u := os.Getenv("USER_NAME")
	log.Printf("user=%s logged in", u)
}

// Negative_const_logprintf: env read but constant message logged.
func Negative_const_logprintf() {
	_ = os.Getenv("USER_NAME")
	log.Printf("user=anon logged in")
}
