package cmd

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestEnsureExecutableSetsMissingBit(t *testing.T) {
	path := filepath.Join(t.TempDir(), "go-ssa-server")
	if err := os.WriteFile(path, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	if err := ensureExecutable(path); err != nil {
		t.Fatal(err)
	}
	info, err := os.Stat(path)
	if err != nil {
		t.Fatal(err)
	}
	if info.Mode()&0o111 == 0 {
		t.Fatalf("mode = %v, want executable", info.Mode())
	}
}

func TestEnsureExecutableLeavesExecutableBinary(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "go-ssa-server")
	if err := os.WriteFile(path, nil, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := ensureExecutable(path); err != nil {
		t.Fatal(err)
	}
	info, err := os.Stat(path)
	if err != nil {
		t.Fatal(err)
	}
	if info.Mode().Perm() != 0o755 {
		t.Fatalf("mode = %v, want unchanged 0755", info.Mode().Perm())
	}
}

func TestEnsureExecutableReportsMissingBinary(t *testing.T) {
	err := ensureExecutable(filepath.Join(t.TempDir(), "missing"))
	if err == nil || !strings.Contains(err.Error(), "was not found") {
		t.Fatalf("error = %v, want not-found", err)
	}
}
