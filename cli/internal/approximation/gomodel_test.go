package approximation

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestValidateGoModel(t *testing.T) {
	write := func(t *testing.T, dir, name, content string) {
		t.Helper()
		if err := os.WriteFile(filepath.Join(dir, name), []byte(content), 0o644); err != nil {
			t.Fatal(err)
		}
	}

	valid := t.TempDir()
	write(t, valid, "go.mod", "module opentaint\n\ngo 1.25.0\n")
	if err := ValidateGoModel(valid); err != nil {
		t.Fatalf("valid model: %v", err)
	}
	nested := t.TempDir()
	write(t, nested, "go.mod", "module opentaint/net\n")
	if err := ValidateGoModel(nested); err != nil {
		t.Fatalf("model below opentaint: %v", err)
	}

	wrongModule := t.TempDir()
	write(t, wrongModule, "go.mod", "module opentaintx\n")
	java := t.TempDir()
	write(t, java, "build.gradle.kts", "")
	file := filepath.Join(t.TempDir(), "go.mod")
	write(t, filepath.Dir(file), "go.mod", "module opentaint\n")

	for name, tc := range map[string]struct{ path, want string }{
		"missing":      {filepath.Join(t.TempDir(), "missing"), "no such file"},
		"file":         {file, "not a directory"},
		"empty":        {t.TempDir(), "has no go.mod"},
		"java":         {java, "--dataflow-approximations"},
		"wrong module": {wrongModule, `must be "opentaint"`},
	} {
		t.Run(name, func(t *testing.T) {
			err := ValidateGoModel(tc.path)
			if err == nil || !strings.Contains(err.Error(), tc.want) {
				t.Fatalf("error = %v, want %q", err, tc.want)
			}
		})
	}
}
