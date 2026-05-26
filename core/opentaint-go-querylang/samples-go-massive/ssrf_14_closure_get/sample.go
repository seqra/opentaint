package util

import (
	"net/http"
)

var r *http.Request

// Positive_closure: closure captures tainted URL by reference, then invokes http.Get.
func Positive_closure() {
	u := r.URL.Query().Get("u")
	doFetch := func() {
		_, _ = http.Get(u)
	}
	doFetch()
}

// Negative_closure_const: closure ignores capture and uses constant URL.
func Negative_closure_const() {
	u := r.URL.Query().Get("u")
	_ = u
	doFetch := func() {
		_, _ = http.Get("https://internal.svc/cb")
	}
	doFetch()
}
