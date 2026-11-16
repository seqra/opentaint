package cmd

import (
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/utils/project"
)

// These tests cover only the --go-server-binary branch of EnsureGoServerAvailable, which
// downloads nothing.

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
	if !strings.Contains(err.Error(), "does not exist") {
		t.Errorf("error should say that the binary does not exist, got: %v", err)
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

func TestEnsureGoServerAvailable_BinaryOverrideNotExecutable(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("windows has no executable bit")
	}
	orig := globals.Config.GoServer.Binary
	t.Cleanup(func() { globals.Config.GoServer.Binary = orig })

	binary := filepath.Join(t.TempDir(), "go-ssa-server")
	if err := os.WriteFile(binary, []byte("#!/bin/sh\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	globals.Config.GoServer.Binary = binary

	_, err := EnsureGoServerAvailable()
	var notExecutable notExecutableError
	if !errors.As(err, &notExecutable) || notExecutable.path != binary {
		t.Fatalf("error = %v, want notExecutableError for %s", err, binary)
	}
	if info, statErr := os.Stat(binary); statErr != nil || info.Mode()&0o111 != 0 {
		t.Errorf("the override was changed: %v, %v", info.Mode(), statErr)
	}
}

// The project model decides whether the analyzer needs go-ssa-server, whatever is on disk.
func TestGoServerEnvWithoutGoProjects(t *testing.T) {
	orig := globals.Config.GoServer.Binary
	t.Cleanup(func() { globals.Config.GoServer.Binary = orig })
	globals.Config.GoServer.Binary = filepath.Join(t.TempDir(), "does-not-exist")

	config := &project.Config{JavaProjects: []project.JavaProject{{SourceRoot: "java_0/sources"}}}
	if env := goServerEnv(config); env != nil {
		t.Errorf("goServerEnv() = %v, want none for a model without Go projects", env)
	}
}

func TestGoServerEnvPointsAtTheGoServer(t *testing.T) {
	if _, err := exec.LookPath("go"); err != nil {
		t.Skip("no Go toolchain")
	}
	orig := globals.Config.GoServer.Binary
	t.Cleanup(func() { globals.Config.GoServer.Binary = orig })
	bin := filepath.Join(t.TempDir(), "go-ssa-server")
	if err := os.WriteFile(bin, []byte("#!/bin/sh\n"), 0o755); err != nil {
		t.Fatal(err)
	}
	globals.Config.GoServer.Binary = bin

	config := &project.Config{GoProjects: []project.GoProject{{ProjectDir: "go_0"}}}
	if got := goServerEnv(config)["GOIR_SERVER_BINARY"]; got != bin {
		t.Errorf("GOIR_SERVER_BINARY = %q, want %q", got, bin)
	}
}
