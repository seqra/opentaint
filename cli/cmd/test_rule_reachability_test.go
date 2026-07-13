package cmd

import (
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/spf13/viper"
)

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

func TestReachabilityExplicitFlagsSurviveConfig(t *testing.T) {
	origTimeout := globals.Config.Scan.Timeout
	origMaxMemory := globals.Config.Scan.MaxMemory
	t.Cleanup(func() {
		globals.Config.Scan.Timeout = origTimeout
		globals.Config.Scan.MaxMemory = origMaxMemory
		globals.ConfigFile = ""
		viper.Reset()
		testRuleReachabilityCmd.Flags().Lookup("timeout").Changed = false
		testRuleReachabilityCmd.Flags().Lookup("max-memory").Changed = false
	})

	cfgFile := filepath.Join(t.TempDir(), "config.yaml")
	if err := os.WriteFile(cfgFile, []byte("scan:\n  timeout: 300s\n  max_memory: 4G\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	globals.ConfigFile = cfgFile

	if err := testRuleReachabilityCmd.Flags().Set("timeout", "777s"); err != nil {
		t.Fatal(err)
	}
	if err := testRuleReachabilityCmd.Flags().Set("max-memory", "16G"); err != nil {
		t.Fatal(err)
	}

	initConfig(testRuleReachabilityCmd)

	if got := globals.Config.Scan.Timeout; got != 777*time.Second {
		t.Errorf("Timeout = %v, want 777s (explicit flag must beat config file)", got)
	}
	if got := globals.Config.Scan.MaxMemory; got != "16G" {
		t.Errorf("MaxMemory = %q, want 16G (explicit flag must beat config file)", got)
	}
}

func TestScanConfigFileAppliesWhenFlagUnset(t *testing.T) {
	origTimeout := globals.Config.Scan.Timeout
	t.Cleanup(func() {
		globals.Config.Scan.Timeout = origTimeout
		globals.ConfigFile = ""
		viper.Reset()
	})

	cfgFile := filepath.Join(t.TempDir(), "config.yaml")
	if err := os.WriteFile(cfgFile, []byte("scan:\n  timeout: 123s\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	globals.ConfigFile = cfgFile

	initConfig(scanCmd)

	if got := globals.Config.Scan.Timeout; got != 123*time.Second {
		t.Errorf("Timeout = %v, want config-file 123s when flag not passed", got)
	}
}
