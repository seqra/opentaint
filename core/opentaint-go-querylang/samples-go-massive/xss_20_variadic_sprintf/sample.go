package util

import (
	"fmt"
	"net/http"
)

var r *http.Request
var w http.ResponseWriter

// Positive_variadic: tainted form value flows as one of multiple variadic args into fmt.Sprintf.
func Positive_variadic() {
	user := r.FormValue("user")
	role := r.FormValue("role")
	body := fmt.Sprintf("<div>user=%s role=%s</div>", user, role)
	w.Write([]byte(body))
}

// Negative_variadic_const: variadic args are constants.
func Negative_variadic_const() {
	_ = r.FormValue("user")
	_ = r.FormValue("role")
	body := fmt.Sprintf("<div>user=%s role=%s</div>", "anon", "guest")
	w.Write([]byte(body))
}
