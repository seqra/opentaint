package testapprox

import (
	_ "embed"
	"fmt"
	"os"
	"path/filepath"

	"github.com/seqra/opentaint/internal/utils"
)

const fixedRuleFileName = "approximation-rule.yaml"

//go:embed example/approximation-rule.yaml
var fixedRule []byte

//go:embed example/src/main/java/test/Taint.java
var taintJava []byte

func WriteFixedRule(dir string) (string, error) {
	path := filepath.Join(dir, fixedRuleFileName)
	if err := os.WriteFile(path, fixedRule, 0o644); err != nil {
		return "", fmt.Errorf("write fixed approximation rule: %w", err)
	}
	return path, nil
}

func Scaffold(projectDir string) error {
	return utils.WriteFiles(map[string][]byte{
		filepath.Join(projectDir, fixedRuleFileName):                           fixedRule,
		filepath.Join(projectDir, "src", "main", "java", "test", "Taint.java"): taintJava,
	})
}
