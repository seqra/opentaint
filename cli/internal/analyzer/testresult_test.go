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

func TestLoadGoTestResult(t *testing.T) {
	path := filepath.Join(t.TempDir(), "test-result.json")
	content := `{
  "success": [],
  "falseNegative": [{"function": "test/security/cmdi.PositiveExec", "ruleId": "go/security/cmdi.yaml#command-injection", "language": "go", "testSetName": "default"}],
  "falsePositive": [], "skipped": [], "disabled": []
}`
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}

	tr, err := LoadTestResult(path)
	if err != nil {
		t.Fatalf("LoadTestResult: %v", err)
	}
	sample := tr.FalseNegative[0]
	if got := sample.Name(); got != "test/security/cmdi.PositiveExec" {
		t.Errorf("Name() = %q, want the function", got)
	}
	if got := sample.RuleID(); got != "go/security/cmdi.yaml:command-injection" {
		t.Errorf("RuleID() = %q, want the --rule-id form", got)
	}
}

func TestJavaSampleRuleID(t *testing.T) {
	sample := TestSampleInfo{ClassName: "test.Sqli", Rule: TestRuleInfo{RulePath: "java/security/sqli.yaml", RuleID: "sql-injection"}}
	if got := sample.RuleID(); got != "java/security/sqli.yaml:sql-injection" {
		t.Errorf("RuleID() = %q, want java/security/sqli.yaml:sql-injection", got)
	}
}

func TestLoadTestResultMissingFile(t *testing.T) {
	if _, err := LoadTestResult(filepath.Join(t.TempDir(), "nope.json")); err == nil {
		t.Fatal("expected error for missing file")
	}
}
