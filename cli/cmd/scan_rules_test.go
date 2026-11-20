package cmd

import (
	"slices"
	"testing"

	"github.com/seqra/opentaint/internal/rules"
)

func TestRuleSelectionFlagsReplaceTheConfig(t *testing.T) {
	cfg := ScanConfig{RuleID: []string{"cmdi"}, ExcludeRuleID: nil}
	got := ruleSelection(cfg)
	if !slices.Equal(got.Only, []string{"cmdi"}) || len(got.Exclude) != 0 {
		t.Errorf("ruleSelection() = %+v, want only [cmdi]", got)
	}
}

func TestNoRulesCauseNamesWhatTheUserSet(t *testing.T) {
	all := []string{"go/security/cmdi.yaml:command-injection"}
	tests := []struct {
		cfg       ScanConfig
		selection rules.Selection
		want      string
	}{
		{ScanConfig{RuleID: []string{"typo"}}, rules.Selection{Only: []string{"typo"}}, "no rule matches --rule-id"},
		{ScanConfig{RuleID: []string{"command-injection"}, ExcludeRuleID: []string{"**"}},
			rules.Selection{Only: []string{"command-injection"}, Exclude: []string{"**"}},
			"--exclude-rule-id excludes every rule that --rule-id selects"},
		{ScanConfig{}, rules.Selection{Exclude: []string{"**"}}, "rules.exclude excludes every rule"},
		{ScanConfig{}, rules.Selection{Only: []string{"typo"}}, "no rule matches rules.only"},
		{ScanConfig{RuleID: []string{"typo"}, RuleIDName: "<rule-id>"}, rules.Selection{Only: []string{"typo"}}, "no rule matches <rule-id>"},
	}
	for _, tt := range tests {
		if got := noRulesCause(tt.cfg, tt.selection, all).Error(); got != tt.want {
			t.Errorf("noRulesCause(%+v) = %q, want %q", tt.selection, got, tt.want)
		}
	}
}
