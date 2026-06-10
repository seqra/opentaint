package analyzer

import (
	"encoding/json"
	"fmt"
	"os"
)

// TestSampleInfo identifies one annotated sample in a rule-test run, as
// serialized by the analyzer's TestProjectAnalyzer into test-result.json.
type TestSampleInfo struct {
	ClassName  string `json:"className"`
	MethodName string `json:"methodName"`
}

// TestResult mirrors the analyzer's test-result.json. The analyzer process
// exits 0 even when samples fail; the verdict lives only in this file.
type TestResult struct {
	Success       []TestSampleInfo `json:"success"`
	FalseNegative []TestSampleInfo `json:"falseNegative"`
	FalsePositive []TestSampleInfo `json:"falsePositive"`
	Skipped       []TestSampleInfo `json:"skipped"`
	Disabled      []TestSampleInfo `json:"disabled"`
}

// Failed counts the samples that keep a run from passing: missed positives,
// false positives, and samples skipped because their rule never loaded.
func (tr *TestResult) Failed() int {
	return len(tr.FalseNegative) + len(tr.FalsePositive) + len(tr.Skipped)
}

// LoadTestResult reads a test-result.json produced by the analyzer's rule-test mode.
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
