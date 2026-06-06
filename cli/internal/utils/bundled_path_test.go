package utils

import (
	"os"
	"path/filepath"
	"testing"
)

// FHS layout: `make install` puts the binary in <prefix>/bin and the artifacts
// in <prefix>/lib, so lib is a sibling of the binary's directory.
func TestResolveBundledDir_FHSLayout(t *testing.T) {
	prefix := t.TempDir()
	binDir := filepath.Join(prefix, "bin")
	libDir := filepath.Join(prefix, "lib")
	if err := os.MkdirAll(binDir, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.MkdirAll(libDir, 0o755); err != nil {
		t.Fatal(err)
	}

	if got := resolveBundledDir(binDir, "lib"); got != libDir {
		t.Errorf("resolveBundledDir(FHS) = %q, want %q (sibling lib)", got, libDir)
	}
}

// Flat layout: the managed install (~/.opentaint/install/) keeps the binary,
// lib/ and jre/ in the same directory.
func TestResolveBundledDir_FlatLayout(t *testing.T) {
	dir := t.TempDir()
	libDir := filepath.Join(dir, "lib")
	if err := os.MkdirAll(libDir, 0o755); err != nil {
		t.Fatal(err)
	}

	if got := resolveBundledDir(dir, "lib"); got != libDir {
		t.Errorf("resolveBundledDir(flat) = %q, want %q", got, libDir)
	}
}

// When neither layout has the directory, fall back to the flat path so callers
// keep a stable default probe/download target (preserves prior behavior).
func TestResolveBundledDir_NoneFallsBackToFlat(t *testing.T) {
	binDir := filepath.Join(t.TempDir(), "bin")
	if err := os.MkdirAll(binDir, 0o755); err != nil {
		t.Fatal(err)
	}

	got := resolveBundledDir(binDir, "jre")
	want := filepath.Join(binDir, "jre")
	if got != want {
		t.Errorf("resolveBundledDir(none) = %q, want %q (flat default)", got, want)
	}
}

func TestResolveBundledDir_EmptyExeDir(t *testing.T) {
	if got := resolveBundledDir("", "lib"); got != "" {
		t.Errorf("resolveBundledDir(\"\") = %q, want empty", got)
	}
}
