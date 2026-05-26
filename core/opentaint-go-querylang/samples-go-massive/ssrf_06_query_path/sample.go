package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Positive_pathcomp: query "path" used as URL path; attacker can use
// "..//evil.com/x" or absolute-form to redirect host on some clients.
func Positive_pathcomp() {
	p := r.URL.Query().Get("path")
	p = strings.TrimLeft(p, "/")
	u := "https://api.internal/" + p
	_, _ = http.Get(u)
}

// Negative_pathcomp_dropped: tainted path computed but not used in fetch.
func Negative_pathcomp_dropped() {
	p := r.URL.Query().Get("path")
	_ = strings.TrimLeft(p, "/")
	_, _ = http.Get("https://api.internal/health")
}
