package util

import (
	"fmt"
	"net/http"
	"os"
)

var r *http.Request

// Positive_merge_env: env supplies host, query supplies path; either source alone
// is enough to flag.
func Positive_merge_env() {
	host := os.Getenv("UPSTREAM_HOST")
	path := r.URL.Query().Get("p")
	u := fmt.Sprintf("https://%s/%s", host, path)
	_, _ = http.Get(u)
}

// Positive_merge_query_only: only the query reaches the URL — still tainted.
func Positive_merge_query_only() {
	_ = os.Getenv("UPSTREAM_HOST")
	path := r.URL.Query().Get("p")
	_, _ = http.Get("https://internal.svc/" + path)
}

// Negative_merge_neither: both sources read but URL is constant.
func Negative_merge_neither() {
	_ = os.Getenv("UPSTREAM_HOST")
	_ = r.URL.Query().Get("p")
	_, _ = http.Get("https://internal.svc/v1/health")
}
