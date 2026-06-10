package analyzer

import (
	"os"
	"path/filepath"
	"testing"
)

func TestLoadTestResult(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "test-result.json")
	content := `{
  "success": [{"className": "test.Ok", "methodName": "m", "rule": {"ruleId": "r1"}}],
  "falseNegative": [{"className": "test.Missed", "methodName": null, "rule": {"ruleId": "r2"}}],
  "falsePositive": [],
  "skipped": [{"className": "test.NoRule", "methodName": "x", "rule": {"ruleId": "gone"}}],
  "disabled": []
}`
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}

	tr, err := LoadTestResult(path)
	if err != nil {
		t.Fatalf("LoadTestResult: %v", err)
	}
	if len(tr.Success) != 1 || tr.Success[0].ClassName != "test.Ok" {
		t.Errorf("Success = %+v, want one test.Ok entry", tr.Success)
	}
	if got := tr.Failed(); got != 2 {
		t.Errorf("Failed() = %d, want 2 (1 falseNegative + 1 skipped)", got)
	}
}

func TestLoadTestResultMissingFile(t *testing.T) {
	if _, err := LoadTestResult(filepath.Join(t.TempDir(), "nope.json")); err == nil {
		t.Fatal("expected error for missing file")
	}
}
