package testmodel

import (
	_ "embed"
	"fmt"
	"os"
	"path/filepath"

	"github.com/seqra/opentaint/internal/testproject"
	"github.com/seqra/opentaint/internal/utils"
)

const fixedRuleFileName = "model-rule.yaml"

//go:embed example/model-rule.yaml
var fixedRule []byte

//go:embed example/src/main/java/test/Taint.java
var taintJava []byte

//go:embed example/rule-test.yaml
var ruleTestTemplate []byte

//go:embed example/go/model-rule.yaml
var fixedGoRule []byte

//go:embed example/go/taint/taint.go
var taintGo []byte

//go:embed example/go/rule-test.yaml
var goRuleTestTemplate []byte

// WriteFixedRule writes the fixed rule for the samples in language, java or go, to dir.
func WriteFixedRule(dir, language string) (string, error) {
	rule := fixedRule
	if language == "go" {
		rule = fixedGoRule
	}
	path := filepath.Join(dir, fixedRuleFileName)
	if err := os.WriteFile(path, rule, 0o644); err != nil {
		return "", fmt.Errorf("write fixed model rule: %w", err)
	}
	return path, nil
}

// IsTestProject reports whether dir is a model test project: it holds the fixed rule.
func IsTestProject(dir string) bool {
	info, err := os.Stat(filepath.Join(dir, fixedRuleFileName))
	return err == nil && !info.IsDir()
}

func Scaffold(projectDir string) error {
	if err := utils.WriteFiles(map[string][]byte{
		filepath.Join(projectDir, fixedRuleFileName):                           fixedRule,
		filepath.Join(projectDir, "src", "main", "java", "test", "Taint.java"): taintJava,
	}); err != nil {
		return err
	}
	return testproject.WriteRuleTestFile(projectDir, ruleTestTemplate)
}

// ScaffoldGo writes the harness of a Go model test project: the taint package, the fixed rule,
// and rule-test.yaml.
func ScaffoldGo(projectDir string) error {
	if err := utils.WriteFiles(map[string][]byte{
		filepath.Join(projectDir, fixedRuleFileName):   fixedGoRule,
		filepath.Join(projectDir, "taint", "taint.go"): taintGo,
	}); err != nil {
		return err
	}
	return testproject.WriteRuleTestFile(projectDir, goRuleTestTemplate)
}
