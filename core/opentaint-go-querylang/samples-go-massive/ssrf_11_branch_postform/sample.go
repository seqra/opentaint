package util

import (
	"net/http"
	"net/url"
)

var r *http.Request

// Positive_branch: tainted URL chosen on one branch; sink reachable via that branch.
func Positive_branch() {
	u := "https://internal.svc/submit"
	if r.URL.Query().Get("mode") == "remote" {
		u = r.URL.Query().Get("dest")
	}
	_, _ = http.PostForm(u, url.Values{"k": {"v"}})
}

// Negative_branch_const: both branches use literal URLs.
func Negative_branch_const() {
	u := "https://internal.svc/submit"
	if r.URL.Query().Get("mode") == "remote" {
		u = "https://internal.svc/submit-remote"
	}
	_, _ = http.PostForm(u, url.Values{"k": {"v"}})
}
