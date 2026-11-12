package testproject

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"golang.org/x/mod/modfile"
)

func TestBootstrapGoWritesModule(t *testing.T) {
	dir := t.TempDir()

	if err := BootstrapGo(dir, "test", []string{"github.com/acme/library@v1.2.3"}); err != nil {
		t.Fatalf("BootstrapGo: %v", err)
	}

	content, err := os.ReadFile(filepath.Join(dir, "go.mod"))
	if err != nil {
		t.Fatal(err)
	}
	file, err := modfile.Parse("go.mod", content, nil)
	if err != nil {
		t.Fatal(err)
	}
	if file.Module.Mod.Path != "test" {
		t.Errorf("module = %q, want test", file.Module.Mod.Path)
	}
	if file.Go == nil || file.Go.Version != GoVersion() {
		t.Errorf("Go version = %v, want %s", file.Go, GoVersion())
	}
	if len(file.Require) != 1 || file.Require[0].Mod.String() != "github.com/acme/library@v1.2.3" {
		t.Errorf("require = %v, want github.com/acme/library@v1.2.3", file.Require)
	}
}

func TestBootstrapGoRejectsMavenCoordinate(t *testing.T) {
	if err := BootstrapGo(t.TempDir(), "test", []string{"com.foo:bar:1.0"}); err == nil {
		t.Fatal("BootstrapGo accepted a Maven coordinate")
	}
}

func TestTidyGo(t *testing.T) {
	if _, err := exec.LookPath("go"); err != nil {
		t.Skip("no Go toolchain")
	}
	dir := t.TempDir()
	writeGoFile(t, filepath.Join(dir, "go.mod"), "module test\n")
	writeGoFile(t, filepath.Join(dir, "sample.go"), "package test\n")
	if err := TidyGo(dir); err != nil {
		t.Fatalf("TidyGo: %v", err)
	}
	content, err := os.ReadFile(filepath.Join(dir, "go.mod"))
	if err != nil {
		t.Fatal(err)
	}
	// Tidy records the language version a go.mod is missing.
	if file, err := modfile.Parse("go.mod", content, nil); err != nil || file.Go == nil {
		t.Errorf("go.mod was not tidied:\n%s", content)
	}

	broken := t.TempDir()
	writeGoFile(t, filepath.Join(broken, "go.mod"), "modul test\n")
	err = TidyGo(broken)
	if err == nil || !strings.Contains(err.Error(), "unknown directive") || !strings.Contains(err.Error(), broken) {
		t.Errorf("error = %v, want the go command output and the directory", err)
	}
}

func TestBuildGo(t *testing.T) {
	if _, err := exec.LookPath("go"); err != nil {
		t.Skip("no Go toolchain")
	}
	dir := t.TempDir()
	writeGoFile(t, filepath.Join(dir, "go.mod"), "module test\n\ngo 1.21\n")
	writeGoFile(t, filepath.Join(dir, "main.go"), "package main\n\nfunc main() {}\n")
	if err := BuildGo(dir); err != nil {
		t.Fatalf("BuildGo: %v", err)
	}
	// The executable of a main package is not left in the test project.
	if _, err := os.Stat(filepath.Join(dir, "test")); !os.IsNotExist(err) {
		t.Errorf("BuildGo wrote an executable into %s", dir)
	}

	writeGoFile(t, filepath.Join(dir, "broken.go"), "package main\n\nfunc broken() { undefinedCall() }\n")
	err := BuildGo(dir)
	if err == nil || !strings.Contains(err.Error(), "'go build ./...' failed in "+dir) ||
		!strings.Contains(err.Error(), "undefined: undefinedCall") {
		t.Errorf("error = %v, want the compile error and the directory", err)
	}
}

func writeGoFile(t *testing.T, path, content string) {
	t.Helper()
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}
}
