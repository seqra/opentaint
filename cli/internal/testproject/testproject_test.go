package testproject

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestBootstrapWritesGradleLayout(t *testing.T) {
	dir := t.TempDir()

	if err := Bootstrap(dir, "my-test-project", []string{"com.foo:bar:1.0"}); err != nil {
		t.Fatalf("Bootstrap: %v", err)
	}

	build, err := os.ReadFile(filepath.Join(dir, "build.gradle.kts"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(build), `compileOnly("com.foo:bar:1.0")`) {
		t.Errorf("build.gradle.kts missing dependency, got:\n%s", build)
	}

	settings, err := os.ReadFile(filepath.Join(dir, "settings.gradle.kts"))
	if err != nil {
		t.Fatal(err)
	}
	if want := `rootProject.name = "my-test-project"`; !strings.Contains(string(settings), want) {
		t.Errorf("settings.gradle.kts missing %q, got:\n%s", want, settings)
	}
}
