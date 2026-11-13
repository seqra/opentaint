package cmd

import (
	"os"
	"path/filepath"
	"runtime"
	"testing"
)

func TestEnsureExecutableSetsMissingBits(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("windows has no executable bits")
	}
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
	if info.Mode().Perm() != 0o755 {
		t.Fatalf("mode = %v, want 0755", info.Mode().Perm())
	}
}

// A release that root installed has an executable binary that the user cannot chmod.
func TestEnsureExecutableLeavesExecutableBinary(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("windows has no executable bits")
	}
	if os.Geteuid() == 0 {
		t.Skip("root can chmod any file")
	}
	info, err := os.Stat("/bin/sh")
	if err != nil || info.Mode()&0o111 == 0 {
		t.Skip("no executable /bin/sh")
	}
	link := filepath.Join(t.TempDir(), "go-ssa-server")
	if err := os.Symlink("/bin/sh", link); err != nil {
		t.Fatal(err)
	}
	if err := ensureExecutable(link); err != nil {
		t.Fatal(err)
	}
}

func TestEnsureExecutableReportsMissingBinary(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("windows has no executable bits")
	}
	if err := ensureExecutable(filepath.Join(t.TempDir(), "missing")); err == nil {
		t.Fatal("got no error for a missing binary")
	}
}
