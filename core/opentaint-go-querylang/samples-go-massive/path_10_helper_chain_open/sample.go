package util

import (
	"net/http"
	"os"
	"strings"
)

var r *http.Request

// helper1 normalizes a name by lower-casing.
func helper1(s string) string { return strings.ToLower(s) }

// helper2 prefixes a base data directory.
func helper2(s string) string { return "/var/data/" + s }

// Positive_chain: form -> helper1 -> helper2 -> os.Open.
func Positive_chain() {
	raw := r.FormValue("name")
	a := helper1(raw)
	b := helper2(a)
	f, _ := os.Open(b)
	_ = f
}

// Negative_const_chain: helpers called with a constant input.
func Negative_const_chain() {
	_ = r.FormValue("name")
	a := helper1("static")
	b := helper2(a)
	f, _ := os.Open(b)
	_ = f
}
