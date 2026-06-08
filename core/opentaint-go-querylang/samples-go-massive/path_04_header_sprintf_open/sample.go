package util

import (
	"fmt"
	"net/http"
	"os"
)

var r *http.Request

// Positive_header: header value formatted into a path string and opened.
func Positive_header() {
	tenant := r.Header.Get("X-Tenant")
	p := fmt.Sprintf("/var/tenants/%s/data.bin", tenant)
	f, _ := os.Open(p)
	_ = f
}

// Negative_const: header read but a constant path is used.
func Negative_const() {
	_ = r.Header.Get("X-Tenant")
	p := fmt.Sprintf("/var/tenants/%s/data.bin", "static")
	f, _ := os.Open(p)
	_ = f
}
