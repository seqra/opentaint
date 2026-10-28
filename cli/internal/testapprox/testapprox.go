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

//go:embed example/go/approximation-rule.yaml
var fixedGoRule []byte

//go:embed example/go/taint/taint.go
var taintGo []byte

// WriteFixedRule writes the fixed source-to-sink rule for language ("java" or "go") to dir.
func WriteFixedRule(dir, language string) (string, error) {
	rule := fixedRule
	if language == "go" {
		rule = fixedGoRule
	}
	path := filepath.Join(dir, fixedRuleFileName)
	if err := os.WriteFile(path, rule, 0o644); err != nil {
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

// ScaffoldGo writes the Go harness: the taint package and the fixed rule.
func ScaffoldGo(projectDir string) error {
	return utils.WriteFiles(map[string][]byte{
		filepath.Join(projectDir, fixedRuleFileName):   fixedGoRule,
		filepath.Join(projectDir, "taint", "taint.go"): taintGo,
	})
}
