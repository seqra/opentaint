package util

import (
	"net/http"
)

var r *http.Request

// Positive_concat: attacker host concatenated after literal scheme; still SSRF
// since host (and possibly path) come from user input.
func Positive_concat() {
	host := r.URL.Query().Get("h")
	u := "https://" + host + "/probe"
	_, _ = http.Get(u)
}

// Negative_concat_const: only literals concatenated.
func Negative_concat_const() {
	_ = r.URL.Query().Get("h")
	u := "https://" + "internal.svc" + "/probe"
	_, _ = http.Get(u)
}
