package cmd

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/seqra/opentaint/internal/globals"
)

// The --go-server-binary override short-circuits EnsureGoServerAvailable: when
// globals.Config.GoServer.Binary is set it validates the path exists, returns
// its absolute form, and performs no download. These tests exercise only that
// override branch, so no network access is involved.

func TestEnsureGoServerAvailable_BinaryOverrideReturnsAbsPath(t *testing.T) {
	orig := globals.Config.GoServer.Binary
	t.Cleanup(func() { globals.Config.GoServer.Binary = orig })

	dir := t.TempDir()
	bin := filepath.Join(dir, "go-ssa-server")
	if err := os.WriteFile(bin, []byte("#!/bin/sh\n"), 0o755); err != nil {
		t.Fatal(err)
	}
	globals.Config.GoServer.Binary = bin

	got, err := EnsureGoServerAvailable()
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if !filepath.IsAbs(got) {
		t.Errorf("EnsureGoServerAvailable() = %q, want an absolute path", got)
	}
	want, _ := filepath.Abs(bin)
	if got != want {
		t.Errorf("EnsureGoServerAvailable() = %q, want %q", got, want)
	}
}

func TestEnsureGoServerAvailable_BinaryOverrideRelativePathResolvedToAbs(t *testing.T) {
	orig := globals.Config.GoServer.Binary
	t.Cleanup(func() { globals.Config.GoServer.Binary = orig })

	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "go-ssa-server"), []byte("x"), 0o755); err != nil {
		t.Fatal(err)
	}
	t.Chdir(dir)

	globals.Config.GoServer.Binary = "go-ssa-server" // relative to cwd

	got, err := EnsureGoServerAvailable()
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if !filepath.IsAbs(got) {
		t.Errorf("EnsureGoServerAvailable() = %q, want absolute path from relative override", got)
	}
	if filepath.Base(got) != "go-ssa-server" {
		t.Errorf("EnsureGoServerAvailable() basename = %q, want %q", filepath.Base(got), "go-ssa-server")
	}
}

func TestEnsureGoServerAvailable_BinaryOverrideMissingReturnsError(t *testing.T) {
	orig := globals.Config.GoServer.Binary
	t.Cleanup(func() { globals.Config.GoServer.Binary = orig })

	globals.Config.GoServer.Binary = filepath.Join(t.TempDir(), "does-not-exist")

	got, err := EnsureGoServerAvailable()
	if err == nil {
		t.Fatalf("expected error for non-existent override binary, got path %q", got)
	}
	if !strings.Contains(err.Error(), "not found") {
		t.Errorf("error should mention binary not found, got: %v", err)
	}
}

func TestEnsureGoServerAvailable_BinaryOverrideDirectoryReturnsError(t *testing.T) {
	orig := globals.Config.GoServer.Binary
	t.Cleanup(func() { globals.Config.GoServer.Binary = orig })

	// Point the override at a directory instead of an executable file.
	globals.Config.GoServer.Binary = t.TempDir()

	got, err := EnsureGoServerAvailable()
	if err == nil {
		t.Fatalf("expected error when override points at a directory, got path %q", got)
	}
	if !strings.Contains(err.Error(), "directory") {
		t.Errorf("error should mention the path is a directory, got: %v", err)
	}
}
