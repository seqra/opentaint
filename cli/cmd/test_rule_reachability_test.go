package cmd

import "testing"

func TestReachabilityScanConfigAppliesPresets(t *testing.T) {
	base := ScanConfig{
		Ruleset:  []string{"builtin"},
		Severity: []string{"warning"},
	}

	cfg := reachabilityScanConfig(base, "security/sqli.yaml:sql-injection", "com.example.A#m")

	if len(cfg.RuleID) != 1 || cfg.RuleID[0] != "security/sqli.yaml:sql-injection" {
		t.Fatalf("RuleID = %v, want [security/sqli.yaml:sql-injection]", cfg.RuleID)
	}
	if !cfg.DebugFactReachabilitySarif {
		t.Error("DebugFactReachabilitySarif = false, want true")
	}
	if !cfg.ExpandRuleRefs {
		t.Error("ExpandRuleRefs = false, want true")
	}
	if cfg.DebugRunAnalysisOnSelectedEntryPoints != "com.example.A#m" {
		t.Errorf("entry points = %q, want com.example.A#m", cfg.DebugRunAnalysisOnSelectedEntryPoints)
	}

	// Base scan flags must be preserved, not clobbered by the preset.
	if len(cfg.Ruleset) != 1 || cfg.Ruleset[0] != "builtin" {
		t.Errorf("Ruleset = %v, want base [builtin]", cfg.Ruleset)
	}
	if len(cfg.Severity) != 1 || cfg.Severity[0] != "warning" {
		t.Errorf("Severity = %v, want base [warning]", cfg.Severity)
	}
}

func TestReachabilityScanConfigOmitsEmptyEntryPoint(t *testing.T) {
	cfg := reachabilityScanConfig(ScanConfig{}, "r", "")
	if cfg.DebugRunAnalysisOnSelectedEntryPoints != "" {
		t.Errorf("entry points = %q, want empty when no entry point given", cfg.DebugRunAnalysisOnSelectedEntryPoints)
	}
}
