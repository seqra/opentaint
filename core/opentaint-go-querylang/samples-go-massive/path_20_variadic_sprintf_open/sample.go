package util

import (
	"fmt"
	"net/http"
	"os"
)

var r *http.Request

// Positive_variadic: tainted form value placed in a multi-arg variadic fmt.Sprintf call,
// whose result is opened.
func Positive_variadic() {
	tenant := r.FormValue("tenant")
	name := r.FormValue("doc")
	p := fmt.Sprintf("/srv/%s/%s/%s", "v1", tenant, name)
	f, _ := os.Open(p)
	_ = f
}

// Positive_variadic_single: a single tainted value through fmt.Sprintf.
func Positive_variadic_single() {
	name := r.FormValue("doc")
	p := fmt.Sprintf("/srv/data/%s", name)
	f, _ := os.Open(p)
	_ = f
}

// Negative_const_variadic: fmt.Sprintf called but only with constants; form is unused.
func Negative_const_variadic() {
	_ = r.FormValue("doc")
	p := fmt.Sprintf("/srv/%s/%s", "v1", "static.bin")
	f, _ := os.Open(p)
	_ = f
}
