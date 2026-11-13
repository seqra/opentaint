package analyzer

import (
	"encoding/json"
	"fmt"
	"os"
)

type TestSampleInfo struct {
	ClassName  string       `json:"className"`
	MethodName string       `json:"methodName"`
	Rule       TestRuleInfo `json:"rule"`
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

// Name returns the sample as class#method, or as the class alone when the sample names no method.
func (s TestSampleInfo) Name() string {
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
