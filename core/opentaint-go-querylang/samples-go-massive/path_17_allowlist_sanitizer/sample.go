package util

import (
	"net/http"
	"os"
	"path/filepath"
	"regexp"
)

var r *http.Request

// allowlist returns the input only if it matches a strict whitelist regex; otherwise
// it falls back to a constant. This is the only safe pattern: it actually blocks
// path-traversal payloads like "../../etc/passwd".
var allowRe = regexp.MustCompile(`^[a-z0-9_-]+\.txt$`)

func allowlist(name string) string {
	if allowRe.MatchString(name) {
		return name
	}
	return "default.txt"
}

// Positive_clean_only: filepath.Clean does NOT block "../" traversal — it only
// normalizes the path. The cleaned path is still attacker-controlled and tainted.
// (Clean is intentionally NOT in pattern-sanitizers.)
func Positive_clean_only() {
	name := r.FormValue("doc")
	cleaned := filepath.Clean(name)
	f, _ := os.Open("/srv/docs/" + cleaned)
	_ = f
}

// Positive_raw: tainted name reaches os.Open with no scrubbing at all.
func Positive_raw() {
	name := r.FormValue("doc")
	f, _ := os.Open("/srv/docs/" + name)
	_ = f
}

// Negative_allowlisted: tainted name passed through util.allowlist before use.
// allowlist guarantees a constant fallback if the input doesn't match the regex.
func Negative_allowlisted() {
	name := r.FormValue("doc")
	safe := allowlist(name)
	f, _ := os.Open("/srv/docs/" + safe)
	_ = f
}
