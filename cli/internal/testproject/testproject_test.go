package testproject

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/seqra/opentaint/internal/testutil"
)

func TestBootstrapWritesGradleLayoutAndJar(t *testing.T) {
	dir := t.TempDir()
	jarSrc := filepath.Join(t.TempDir(), testutil.JarName)
	if err := os.WriteFile(jarSrc, []byte("fake-jar"), 0o644); err != nil {
		t.Fatal(err)
	}

	if err := Bootstrap(dir, "my-test-project", []string{"com.foo:bar:1.0"}, jarSrc); err != nil {
		t.Fatalf("Bootstrap: %v", err)
	}

	build, err := os.ReadFile(filepath.Join(dir, "build.gradle.kts"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(build), "libs/"+testutil.JarName) {
		t.Errorf("build.gradle.kts must reference libs/%s, got:\n%s", testutil.JarName, build)
	}
	if !strings.Contains(string(build), `compileOnly("com.foo:bar:1.0")`) {
		t.Errorf("build.gradle.kts missing dependency, got:\n%s", build)
	}
	if _, err := os.Stat(filepath.Join(dir, "libs", testutil.JarName)); err != nil {
		t.Errorf("jar not copied to libs/: %v", err)
	}
	settings, err := os.ReadFile(filepath.Join(dir, "settings.gradle.kts"))
	if err != nil {
		t.Fatal(err)
	}
	if want := `rootProject.name = "my-test-project"`; !strings.Contains(string(settings), want) {
		t.Errorf("settings.gradle.kts missing %q, got:\n%s", want, settings)
	}
}
