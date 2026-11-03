package testmodel

import (
	"os"
	"path/filepath"
	"testing"

	"gopkg.in/yaml.v2"
)

type ruleTests struct {
	Tests []struct {
		RuleID   string   `yaml:"rule-id"`
		Positive []string `yaml:"positive"`
		Negative []string `yaml:"negative"`
	} `yaml:"tests"`
}

type ruleFile struct {
	Rules []struct {
		ID string `yaml:"id"`
	} `yaml:"rules"`
}

// The rule-test.yaml template must point at the fixed rule that test model run applies.
func TestScaffoldWritesRuleTestForTheFixedRule(t *testing.T) {
	dir := t.TempDir()
	if err := Scaffold(dir); err != nil {
		t.Fatalf("Scaffold: %v", err)
	}

	data, err := os.ReadFile(filepath.Join(dir, "rule-test.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	var tests ruleTests
	if err := yaml.Unmarshal(data, &tests); err != nil {
		t.Fatalf("rule-test.yaml is not valid YAML: %v", err)
	}

	var rule ruleFile
	if err := yaml.Unmarshal(fixedRule, &rule); err != nil || len(rule.Rules) != 1 {
		t.Fatalf("fixed rule: %v, %d rules", err, len(rule.Rules))
	}
	want := fixedRuleFileName + "#" + rule.Rules[0].ID
	if len(tests.Tests) != 1 || tests.Tests[0].RuleID != want {
		t.Fatalf("rule-test.yaml tests = %+v, want one test of %s", tests.Tests, want)
	}
	if len(tests.Tests[0].Positive) != 0 || len(tests.Tests[0].Negative) != 0 {
		t.Errorf("the template has samples: %+v", tests.Tests[0])
	}
}
