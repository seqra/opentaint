package cmd

import (
	"errors"
	"os"
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

// fakeGoRoot returns a directory that passes for the Go toolchain of a project model.
func fakeGoRoot(t *testing.T) string {
	t.Helper()
	goRoot := t.TempDir()
	if err := os.MkdirAll(filepath.Join(goRoot, "bin"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(goRoot, "bin", "go"), []byte("#!/bin/sh\n"), 0o755); err != nil {
		t.Fatal(err)
	}
	return goRoot
}

// The project model decides whether the analyzer needs go-ssa-server, whatever is on disk: a
// model without Go projects, or with only Go projects that the analyzer skips, needs none.
func TestGoServerEnvWithoutGoProjectsToAnalyze(t *testing.T) {
	orig := globals.Config.GoServer.Binary
	t.Cleanup(func() { globals.Config.GoServer.Binary = orig })
	globals.Config.GoServer.Binary = filepath.Join(t.TempDir(), "does-not-exist")

	java := []project.JavaProject{{SourceRoot: "java_0/sources"}}
	for name, config := range map[string]*project.Config{
		"no Go projects":       {JavaProjects: java},
		"no Go toolchain":      {JavaProjects: java, GoProjects: []project.GoProject{{ProjectDir: "go_0"}}},
		"missing Go toolchain": {GoProjects: []project.GoProject{{ProjectDir: "go_0", GoToolchain: "/does/not/exist"}}},
	} {
		if env := goServerEnv(config, t.TempDir()); env != nil {
			t.Errorf("%s: goServerEnv() = %v, want none", name, env)
		}
	}
}

func TestGoServerEnvPointsAtTheGoServer(t *testing.T) {
	orig := globals.Config.GoServer.Binary
	t.Cleanup(func() { globals.Config.GoServer.Binary = orig })
	bin := filepath.Join(t.TempDir(), "go-ssa-server")
	if err := os.WriteFile(bin, []byte("#!/bin/sh\n"), 0o755); err != nil {
		t.Fatal(err)
	}
	globals.Config.GoServer.Binary = bin

	config := &project.Config{GoProjects: []project.GoProject{{ProjectDir: "go_0", GoToolchain: fakeGoRoot(t)}}}
	if got := goServerEnv(config, t.TempDir())["GOIR_SERVER_BINARY"]; got != bin {
		t.Errorf("GOIR_SERVER_BINARY = %q, want %q", got, bin)
	}
}

func TestRebuildModelCommand(t *testing.T) {
	origArgs := os.Args
	t.Cleanup(func() { os.Args = origArgs })
	os.Args = []string{"opentaint", "scan", "my project", "--dry-run"}

	cached := rebuildModelCommand(ScanConfig{}, scanPlan{projectCachePath: "/cache/p"})
	if want := "opentaint scan 'my project' --recompile"; cached != want {
		t.Errorf("cached model: %q, want %q", cached, want)
	}
	given := rebuildModelCommand(ScanConfig{ProjectModelPath: "./model"}, scanPlan{})
	if want := "opentaint compile <source-path> --output ./model"; given != want {
		t.Errorf("given model: %q, want %q", given, want)
	}
}

// A rescan of sources reports the paths that the first scan did, though the model comes from the
// cache; a scan of a project model uses the source root of the model.
func TestSarifSourceRoot(t *testing.T) {
	userRoot := t.TempDir()
	model := t.TempDir()
	if err := os.WriteFile(filepath.Join(model, "project.yaml"), []byte("goProjects:\n- projectDir: go_0\n"), 0o644); err != nil {
		t.Fatal(err)
	}

	got, err := sarifSourceRoot(false, userRoot, model)
	if err != nil || got != userRoot {
		t.Errorf("source scan: sarifSourceRoot() = %q, %v, want %q", got, err, userRoot)
	}
	got, err = sarifSourceRoot(true, userRoot, model)
	if err != nil || got != filepath.Join(model, "go_0") {
		t.Errorf("model scan: sarifSourceRoot() = %q, %v, want %q", got, err, filepath.Join(model, "go_0"))
	}
}
