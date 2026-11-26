package cmd

import (
	"fmt"
	"strings"
	"testing"

	"github.com/seqra/opentaint/internal/analyzer"
)

func TestPassedLine(t *testing.T) {
	for _, tc := range []struct {
		kind             string
		passed, disabled int
		want             string
	}{
		{"model", 2, 0, "All 2 model tests passed"},
		{"rule", 1, 0, "1 rule test passed"},
		{"rule", 3, 1, "All 3 rule tests passed, 1 disabled"},
	} {
		if got := passedLine(tc.kind, tc.passed, tc.disabled); got != tc.want {
			t.Errorf("passedLine(%q, %d, %d) = %q, want %q", tc.kind, tc.passed, tc.disabled, got, tc.want)
		}
	}
}

func TestSkippedByRule(t *testing.T) {
	sqli := analyzer.TestRuleInfo{RulePath: "java/security/sqli.yaml", RuleID: "sql-injection"}
	xss := analyzer.TestRuleInfo{RulePath: "java/security/xss.yaml", RuleID: "xss"}
	groups := skippedByRule([]analyzer.TestSampleInfo{
		{ClassName: "com.example.Xss", MethodName: "echo", Rule: xss},
		{ClassName: "com.example.Sqli", MethodName: "concat", Rule: sqli},
		{ClassName: "com.example.Xss", MethodName: "escaped", Rule: xss},
	})
	var got []string
	for _, group := range groups {
		got = append(got, fmt.Sprint(group))
	}
	text := strings.Join(got, "\n")
	for _, want := range []string{"java/security/xss.yaml:xss", "com.example.Xss#echo", "com.example.Xss#escaped", "java/security/sqli.yaml:sql-injection"} {
		if !strings.Contains(text, want) {
			t.Errorf("skippedByRule() has no %q:\n%s", want, text)
		}
	}
	if len(groups) != 2 || strings.Index(text, "xss.yaml") > strings.Index(text, "sqli.yaml") {
		t.Errorf("skippedByRule() = %d groups in the wrong order:\n%s", len(groups), text)
	}
}
