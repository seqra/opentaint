package util

import (
	"net/http"
)

var r *http.Request

// assertAllowedHost returns a fixed safe URL unless the input parses to a
// pre-approved host. This is the recommended SSRF mitigation pattern: an
// allowlist, not an escape function. Note that url.QueryEscape is NOT a valid
// SSRF sanitizer because escaping bytes inside the host still lets the
// attacker control the host.
func assertAllowedHost(u string) string {
	// Simulated allowlist check; in real code would parse and compare host.
	if u == "https://allowed.example.com/x" {
		return u
	}
	return "https://internal.svc/blocked"
}

// Positive_no_sanitizer: tainted URL flows straight to http.Get.
func Positive_no_sanitizer() {
	u := r.URL.Query().Get("u")
	_, _ = http.Get(u)
}

// Negative_with_allowlist: tainted URL passed through allowlist sanitizer.
func Negative_with_allowlist() {
	u := r.URL.Query().Get("u")
	u = assertAllowedHost(u)
	_, _ = http.Get(u)
}
