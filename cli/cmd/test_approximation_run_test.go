package cmd

import (
	"os"
	"path/filepath"
	"testing"
)

func TestProjectModelLanguage(t *testing.T) {
	for name, tc := range map[string]struct{ yaml, want string }{
		"go":      {"goProjects:\n  - projectDir: go_0\n", "go"},
		"java":    {"javaProjects:\n  - sourceRoot: src\n    modules: []\n", "java"},
		"mixed":   {"goProjects:\n  - projectDir: go_0\njavaProjects:\n  - sourceRoot: src\n    modules: []\n", "java"},
		"missing": {"", "java"},
	} {
		t.Run(name, func(t *testing.T) {
			dir := t.TempDir()
			if tc.yaml != "" {
				if err := os.WriteFile(filepath.Join(dir, "project.yaml"), []byte(tc.yaml), 0o644); err != nil {
					t.Fatal(err)
				}
			}
			if got := projectModelLanguage(dir); got != tc.want {
				t.Errorf("projectModelLanguage = %q, want %q", got, tc.want)
			}
		})
	}
}
