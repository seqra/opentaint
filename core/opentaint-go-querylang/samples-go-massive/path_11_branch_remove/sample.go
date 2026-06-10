package util

import (
	"os"
	"strings"
)

// Positive_if_branch: tainted env reaches os.Remove only on the "yes" branch.
func Positive_if_branch() {
	v := os.Getenv("PURGE")
	if strings.HasPrefix(v, "yes:") {
		name := strings.TrimPrefix(v, "yes:")
		_ = os.Remove("/var/cache/" + name)
	}
}

// Negative_other_branch: tainted env, but the os.Remove call uses a constant path on the
// branch that runs; the tainted value is logged-only (no sink).
func Negative_other_branch() {
	v := os.Getenv("PURGE")
	if v == "" {
		_ = os.Remove("/var/cache/empty.tmp")
	} else {
		// taint is silently dropped here (e.g. just length checked)
		_ = len(v)
	}
}
