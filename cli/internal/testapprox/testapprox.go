package testapprox

import (
	_ "embed"
	"fmt"
	"os"
	"path/filepath"

	"github.com/seqra/opentaint/internal/utils"
)

const fixedRuleFileName = "approximation-rule.yaml"

const (
	PlainSourcePlainSinkRuleID     = "approximation-rule-plain-source-plain-sink"
	PlainSourceStarredSinkRuleID   = "approximation-rule-plain-source-starred-sink"
	StarredSourcePlainSinkRuleID   = "approximation-rule-starred-source-plain-sink"
	StarredSourceStarredSinkRuleID = "approximation-rule-starred-source-starred-sink"
)

//go:embed example/approximation-rule.yaml
var fixedRule []byte

//go:embed example/src/main/java/test/Taint.java
var taintJava []byte

func ScopeRuleIDs() []string {
	return []string{
		PlainSourcePlainSinkRuleID,
		PlainSourceStarredSinkRuleID,
		StarredSourcePlainSinkRuleID,
		StarredSourceStarredSinkRuleID,
	}
}

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
