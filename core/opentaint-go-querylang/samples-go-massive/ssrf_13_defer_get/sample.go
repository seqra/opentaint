package util

import (
	"net/http"
	"os"
)

// Positive_defer: deferred callback fetches a tainted URL on function exit.
func Positive_defer() {
	cb := os.Getenv("CALLBACK_URL")
	defer func() {
		_, _ = http.Get(cb)
	}()
	_ = cb
}

// Negative_defer_const: deferred fetch uses a constant URL.
func Negative_defer_const() {
	_ = os.Getenv("CALLBACK_URL")
	defer func() {
		_, _ = http.Get("https://internal.svc/cb")
	}()
}
