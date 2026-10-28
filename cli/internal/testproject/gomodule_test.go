package testproject

import (
	"os"
	"path/filepath"
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
