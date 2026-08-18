package testrule

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestScaffoldWritesPlainAndStarredMarkerRules(t *testing.T) {
	projectDir := t.TempDir()
	if err := Scaffold(projectDir); err != nil {
		t.Fatalf("Scaffold() error = %v", err)
	}

	tests := map[string]string{
		genericSourceRule:        "$UNTRUSTED = test.Taint.source();",
		genericSourceStarredRule: "$*UNTRUSTED = test.Taint.source();",
		genericSinkRule:          "test.Taint.sink($VALUE)",
		genericSinkStarredRule:   "test.Taint.sink($*VALUE)",
	}
	for rule, want := range tests {
		path := filepath.Join(projectDir, markersDir, filepath.FromSlash(rule))
		data, err := os.ReadFile(path)
		if err != nil {
			t.Errorf("read scaffolded marker %q: %v", rule, err)
			continue
		}
		if !strings.Contains(string(data), want) {
			t.Errorf("scaffolded marker %q does not contain %q", rule, want)
		}
	}
}
