// Package testapprox bundles the fixed source->sink rule the `opentaint dev test-approximations`
// harness applies, and the Taint source/sink helper scaffolded into an approximation test project.
package testapprox

import (
	_ "embed"
	"fmt"
	"os"
	"path/filepath"
)

// FixedRuleFileName is the rule's path relative to the ruleset root, and the value
// samples reference in @PositiveRuleSample/@NegativeRuleSample.
const FixedRuleFileName = "approximation-rule.yaml"

// ApproximationsSrcDir is the source root, relative to the project, where the agent writes the
// approximation under test and which is passed to test-approximations as --dataflow-approximations.
const ApproximationsSrcDir = "approximations/src"

//go:embed example/approximation-rule.yaml
var fixedRule []byte

//go:embed example/src/main/java/test/Taint.java
var taintJava []byte

// WriteFixedRule writes the fixed harness rule into dir and returns its path. Used by
// test-approximations to apply the rule automatically from a throwaway ruleset directory.
func WriteFixedRule(dir string) (string, error) {
	path := filepath.Join(dir, FixedRuleFileName)
	if err := os.WriteFile(path, fixedRule, 0o644); err != nil {
		return "", fmt.Errorf("write fixed approximation rule: %w", err)
	}
	return path, nil
}

// Scaffold writes the fixed rule (for reference — test-approximations applies its own bundled copy)
// and the Taint source/sink helper, and creates the approximations source dir for the agent to write
// the approximation under test into. Samples and the approximation itself are the agent's to write.
func Scaffold(projectDir string) error {
	files := map[string][]byte{
		filepath.Join(projectDir, FixedRuleFileName):                           fixedRule,
		filepath.Join(projectDir, "src", "main", "java", "test", "Taint.java"): taintJava,
	}
	for path, content := range files {
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			return fmt.Errorf("create %s: %w", filepath.Dir(path), err)
		}
		if err := os.WriteFile(path, content, 0o644); err != nil {
			return fmt.Errorf("write %s: %w", filepath.Base(path), err)
		}
	}
	approxDir := filepath.Join(projectDir, filepath.FromSlash(ApproximationsSrcDir), "approx")
	if err := os.MkdirAll(approxDir, 0o755); err != nil {
		return fmt.Errorf("create %s: %w", approxDir, err)
	}
	return nil
}
