package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Positive_loop: comma-separated list of attacker URLs split and fetched in a loop.
func Positive_loop() {
	raw := r.FormValue("urls")
	for _, u := range strings.Split(raw, ",") {
		_, _ = http.Get(u)
	}
}

// Negative_loop_const_list: tainted raw read but loop iterates a constant slice.
func Negative_loop_const_list() {
	_ = r.FormValue("urls")
	for _, u := range []string{"https://a.svc/", "https://b.svc/"} {
		_, _ = http.Get(u)
	}
}
