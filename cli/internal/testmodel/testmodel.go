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

func WriteFixedRule(dir string) (string, error) {
	path := filepath.Join(dir, fixedRuleFileName)
	if err := os.WriteFile(path, fixedRule, 0o644); err != nil {
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
