package util

import (
	"net/http"
)

var r *http.Request
var w http.ResponseWriter

// Positive_defer_write: deferred write emits a tainted footer.
func Positive_defer_write() {
	q := r.URL.Query().Get("trace")
	defer w.Write([]byte("<!-- trace=" + q + " -->"))
}

// Negative_defer_const: defer present but only constant footer written.
func Negative_defer_const() {
	_ = r.URL.Query().Get("trace")
	defer w.Write([]byte("<!-- trace=off -->"))
}
