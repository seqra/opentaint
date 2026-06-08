package util

import (
	"log"
	"os"
	"strings"
)

// Positive_env_tolower_logprintf: env passed through strings.ToLower then log.Printf.
func Positive_env_tolower_logprintf() {
	u := os.Getenv("AUDIT")
	lo := strings.ToLower(u)
	log.Printf("audit=%s", lo)
}

// Negative_const_lower: env unused; static lowercase string logged.
func Negative_const_lower() {
	_ = os.Getenv("AUDIT")
	log.Printf("audit=%s", "anon")
}
