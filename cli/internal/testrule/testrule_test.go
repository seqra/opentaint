package testrule

import (
	"os"
	"path/filepath"
	"testing"

	"gopkg.in/yaml.v2"
)

func TestScaffoldWritesAnEmptyRuleTest(t *testing.T) {
	dir := t.TempDir()
	if err := Scaffold(dir); err != nil {
		t.Fatalf("Scaffold: %v", err)
	}

	data, err := os.ReadFile(filepath.Join(dir, "rule-test.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	var doc struct {
		Tests *[]any `yaml:"tests"`
	}
	if err := yaml.Unmarshal(data, &doc); err != nil {
		t.Fatalf("rule-test.yaml is not valid YAML: %v", err)
	}
	if doc.Tests == nil || len(*doc.Tests) != 0 {
		t.Errorf("rule-test.yaml must hold an empty tests list, got:\n%s", data)
	}
}

func TestScaffoldGoWritesMarkers(t *testing.T) {
	dir := t.TempDir()
	if err := ScaffoldGo(dir); err != nil {
		t.Fatalf("ScaffoldGo: %v", err)
	}
	for _, path := range []string{
		filepath.Join("taint", "taint.go"),
		filepath.Join(MarkersDir, filepath.FromSlash(genericGoSourceRule)),
		filepath.Join(MarkersDir, filepath.FromSlash(genericGoSinkRule)),
		"rule-test.yaml",
	} {
		if _, err := os.Stat(filepath.Join(dir, path)); err != nil {
			t.Errorf("missing %s: %v", path, err)
		}
	}
}
