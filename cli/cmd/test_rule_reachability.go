package cmd

import (
	"github.com/spf13/cobra"
)

var reachabilityEntryPoint string

var testRuleReachabilityCmd = &cobra.Command{
	Use:   "reachability <rule-id> [source-path]",
	Short: "Trace why a rule can or cannot reach its facts",
	Long: `Scan a project with one rule and write a sibling fact-reachability SARIF
report (debug-ifds-fact-reachability.sarif) next to the main one. Use this to
debug why a rule does or does not fire.

Referenced library source and sink rules are collected and analyzed automatically.`,
	Annotations: map[string]string{"PrintConfig": "true"},
	Args:        cobra.RangeArgs(1, 2),
	Run: func(cmd *cobra.Command, args []string) {
		if reachabilityEntryPoint != "" {
			out.Warn("on Spring projects this method is added to the auto-discovered entry points, not used to restrict them")
		}
		cfg := reachabilityScanConfig(scanFlags, args[0], reachabilityEntryPoint)
		runScan(cmd, prepareScanConfig(cfg, args[1:]))
	},
}

func reachabilityScanConfig(base ScanConfig, ruleID, entryPoint string) ScanConfig {
	base.RuleID = []string{ruleID}
	base.DebugFactReachabilitySarif = true
	base.ExpandRuleRefs = true
	if entryPoint != "" {
		base.DebugRunAnalysisOnSelectedEntryPoints = entryPoint
	}
	return base
}

func init() {
	testRuleCmd.AddCommand(testRuleReachabilityCmd)
	addScanFlags(testRuleReachabilityCmd)
	testRuleReachabilityCmd.Flags().StringVar(&reachabilityEntryPoint, "entry-points", "",
		"Start analysis from a fully qualified method such as com.example.Class#method")
}
