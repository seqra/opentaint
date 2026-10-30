package testapprox

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestScaffoldGoWritesHarness(t *testing.T) {
	dir := t.TempDir()
	if err := ScaffoldGo(dir); err != nil {
		t.Fatalf("ScaffoldGo: %v", err)
	}
	taint, err := os.ReadFile(filepath.Join(dir, "taint", "taint.go"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(taint), "package taint") {
		t.Errorf("taint.go is not package taint:\n%s", taint)
	}
	rule, err := os.ReadFile(filepath.Join(dir, fixedRuleFileName))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(rule), "- go") || !strings.Contains(string(rule), "id: model-rule") {
		t.Errorf("fixed rule is not the Go model-rule:\n%s", rule)
	}
}

func TestScaffoldWritesJavaHarness(t *testing.T) {
	dir := t.TempDir()
	if err := Scaffold(dir); err != nil {
		t.Fatalf("Scaffold: %v", err)
	}
	if _, err := os.Stat(filepath.Join(dir, "src", "main", "java", "test", "Taint.java")); err != nil {
		t.Error(err)
	}
	rule, err := os.ReadFile(filepath.Join(dir, "model-rule.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(rule), "- java") || !strings.Contains(string(rule), "id: model-rule") {
		t.Errorf("fixed rule is not the Java model-rule:\n%s", rule)
	}
	if !IsTestProject(dir) {
		t.Error("scaffolded directory is not recognized as a model test project")
	}
}

func TestWriteFixedRuleSelectsLanguage(t *testing.T) {
	for language, want := range map[string]string{"java": "test.Taint.source()", "go": "taint.Source()"} {
		path, err := WriteFixedRule(t.TempDir(), language)
		if err != nil {
			t.Fatal(err)
		}
		rule, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		if !strings.Contains(string(rule), want) {
			t.Errorf("%s rule does not match %s:\n%s", language, want, rule)
		}
	}
}
