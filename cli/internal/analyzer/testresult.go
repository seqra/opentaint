package analyzer

import (
	"encoding/json"
	"fmt"
	"os"
)

type TestSampleInfo struct {
	ClassName  string `json:"className"`
	MethodName string `json:"methodName"`
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
