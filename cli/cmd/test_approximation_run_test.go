package cmd

import (
	"strings"
	"testing"

	"github.com/seqra/opentaint/internal/analyzer"
	"github.com/seqra/opentaint/internal/testapprox"
)

func TestValidateRequiredRuleMatrix(t *testing.T) {
	ruleIDs := testapprox.ScopeRuleIDs()
	tr := &analyzer.TestResult{}
	for _, id := range ruleIDs {
		tr.Success = append(tr.Success, matrixSample("test.Sample", "flows", id))
	}

	if err := validateRequiredRuleMatrix(tr, ruleIDs); err != nil {
		t.Fatalf("validateRequiredRuleMatrix: %v", err)
	}
}

func TestValidateRequiredRuleMatrixRejectsMissingScope(t *testing.T) {
	ruleIDs := testapprox.ScopeRuleIDs()
	tr := &analyzer.TestResult{
		Success: []analyzer.TestSampleInfo{
			matrixSample("test.Sample", "flows", ruleIDs[0]),
		},
	}

	err := validateRequiredRuleMatrix(tr, ruleIDs)
	if err == nil {
		t.Fatal("expected incomplete matrix error")
	}
	if want := ruleIDs[1]; !strings.Contains(err.Error(), want) {
		t.Errorf("error %q does not name missing rule %q", err, want)
	}
}

func TestValidateRequiredRuleMatrixRejectsEmptyTests(t *testing.T) {
	err := validateRequiredRuleMatrix(&analyzer.TestResult{}, testapprox.ScopeRuleIDs())
	if err == nil || !strings.Contains(err.Error(), "matrix is empty") {
		t.Fatalf("error = %v, want empty matrix error", err)
	}
}

func matrixSample(className, methodName, ruleID string) analyzer.TestSampleInfo {
	sample := analyzer.TestSampleInfo{ClassName: className, MethodName: methodName}
	sample.Rule.RuleID = ruleID
	return sample
}
