package util

import (
	"net/http"
)

var r *http.Request
var w http.ResponseWriter

// Positive_closure_write: closure captures tainted form value, calls w.Write inside.
func Positive_closure_write() {
	name := r.FormValue("name")
	render := func() {
		w.Write([]byte("<h2>" + name + "</h2>"))
	}
	render()
}

// Negative_closure_const: closure writes only a constant.
func Negative_closure_const() {
	_ = r.FormValue("name")
	render := func() {
		w.Write([]byte("<h2>guest</h2>"))
	}
	render()
}
