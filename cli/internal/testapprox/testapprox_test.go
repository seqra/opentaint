package testapprox

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestScaffoldWritesPlainAndStarredScopeMatrix(t *testing.T) {
	dir := t.TempDir()
	if err := Scaffold(dir); err != nil {
		t.Fatalf("Scaffold: %v", err)
	}

	ruleData, err := os.ReadFile(filepath.Join(dir, fixedRuleFileName))
	if err != nil {
		t.Fatal(err)
	}
	rule := string(ruleData)
	checks := []string{
		"pattern: $UNTRUSTED = test.Taint.source();",
		"pattern: $*UNTRUSTED = test.Taint.source();",
		"pattern: test.Taint.sink($VALUE)",
		"pattern: test.Taint.sink($*VALUE)",
	}
	for _, id := range ScopeRuleIDs() {
		checks = append(checks, "id: "+id)
	}
	for _, want := range checks {
		if !strings.Contains(rule, want) {
			t.Errorf("%s missing %q", fixedRuleFileName, want)
		}
	}

	taintPath := filepath.Join(dir, "src", "main", "java", "test", "Taint.java")
	taintData, err := os.ReadFile(taintPath)
	if err != nil {
		t.Fatal(err)
	}
	taint := string(taintData)
	for _, want := range []string{"public static <T> T source()", "public static void sink(Object value)"} {
		if !strings.Contains(taint, want) {
			t.Errorf("Taint.java missing %q", want)
		}
	}
}
