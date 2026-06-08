package util

import (
	"net/http"
	"os"
)

var r *http.Request

// Positive_closure: outer captures tainted query value, closure uses it inside os.Open.
func Positive_closure() {
	name := r.URL.Query().Get("file")
	open := func() {
		f, _ := os.Open("/srv/" + name)
		_ = f
	}
	open()
}

// Negative_const_closure: query is read but the closure opens a constant.
func Negative_const_closure() {
	_ = r.URL.Query().Get("file")
	open := func() {
		f, _ := os.Open("/srv/static.bin")
		_ = f
	}
	open()
}
