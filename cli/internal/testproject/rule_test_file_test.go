package testproject

import (
	"os"
	"path/filepath"
	"testing"
)

func TestWriteRuleTestFileWritesTemplate(t *testing.T) {
	dir := t.TempDir()
	if err := WriteRuleTestFile(dir, []byte("tests: []\n")); err != nil {
		t.Fatalf("WriteRuleTestFile: %v", err)
	}
	got, err := os.ReadFile(filepath.Join(dir, RuleTestFileName))
	if err != nil {
		t.Fatal(err)
	}
	if string(got) != "tests: []\n" {
		t.Errorf("rule-test.yaml = %q, want the template", got)
	}
}

func TestWriteRuleTestFileKeepsExistingSamples(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, RuleTestFileName)
	existing := "tests:\n  - rule-id: my.yaml#my\n"
	if err := os.WriteFile(path, []byte(existing), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := WriteRuleTestFile(dir, []byte("tests: []\n")); err != nil {
		t.Fatalf("WriteRuleTestFile: %v", err)
	}
	got, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if string(got) != existing {
		t.Errorf("rule-test.yaml = %q, want the existing file kept", got)
	}
}
