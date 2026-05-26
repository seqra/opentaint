package util

import (
	"fmt"
	"net/http"
)

var r *http.Request

// Positive_variadic: tainted form values passed as interface{} variadic
// to fmt.Sprintf; result is fetched. Taint must survive the interface{}
// boxing of the variadic args.
func Positive_variadic() {
	host := r.FormValue("h")
	path := r.FormValue("p")
	u := fmt.Sprintf("https://%s/%s", host, path)
	_, _ = http.Get(u)
}

// Negative_variadic_dropped: same Sprintf but result discarded; fetch is constant.
func Negative_variadic_dropped() {
	host := r.FormValue("h")
	path := r.FormValue("p")
	_ = fmt.Sprintf("https://%s/%s", host, path)
	_, _ = http.Get("https://internal.svc/v1/data")
}
