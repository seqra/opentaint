package analyzer

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"
)

// TestSampleInfo is a test sample in test-result.json. A Java sample has a class, a method and a
// rule; a Go sample has a function and a rule ID.
type TestSampleInfo struct {
	ClassName  string       `json:"className"`
	MethodName string       `json:"methodName"`
	Rule       TestRuleInfo `json:"rule"`
	Function   string       `json:"function"`
	GoRuleID   string       `json:"ruleId"`
}

// TestRuleInfo is the rule that a test sample checks.
type TestRuleInfo struct {
	RulePath string `json:"rulePath"`
	RuleID   string `json:"ruleId"`
}

// ID returns the rule ID in the form that --rule-id takes: <rule-path>:<rule-id>, or the rule path
// alone when the test names no rule in the file.
func (r TestRuleInfo) ID() string {
	if r.RuleID == "" {
		return r.RulePath
	}
	return r.RulePath + ":" + r.RuleID
}

// RuleID returns the ID of the rule of the sample in the form that --rule-id takes. A Go rule ID
// is <rule-path>#<rule-id>, and the analyzer reads it with ":" in place of "#".
func (s TestSampleInfo) RuleID() string {
	if s.GoRuleID != "" {
		return strings.ReplaceAll(s.GoRuleID, "#", ":")
	}
	return s.Rule.ID()
}

// Name returns a Go sample as its function, and a Java sample as class#method, or as the class
// alone when the sample names no method.
func (s TestSampleInfo) Name() string {
	if s.Function != "" {
		return s.Function
	}
	if s.MethodName == "" {
		return s.ClassName
	}
	return s.ClassName + "#" + s.MethodName
}

type TestResult struct {
	Success       []TestSampleInfo `json:"success"`
	FalseNegative []TestSampleInfo `json:"falseNegative"`
	FalsePositive []TestSampleInfo `json:"falsePositive"`
	Skipped       []TestSampleInfo `json:"skipped"`
	Disabled      []TestSampleInfo `json:"disabled"`
}

func (tr *TestResult) Failed() int {
	return len(tr.FalseNegative) + len(tr.FalsePositive) + len(tr.Skipped)
}

func LoadTestResult(path string) (*TestResult, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var tr TestResult
	if err := json.Unmarshal(data, &tr); err != nil {
		return nil, fmt.Errorf("parse %s: %w", path, err)
	}
	return &tr, nil
}
