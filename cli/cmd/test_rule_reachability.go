package cmd

import (
	"github.com/spf13/cobra"
)

var reachabilityEntryPoint string

var testRuleReachabilityCmd = &cobra.Command{
	Use:   "reachability <rule-id> [source-path]",
	Short: "Trace why a rule can or cannot reach its facts",
	Long: `Scan a project with a single rule and write a fact-reachability SARIF report so you can see why that rule does or does not fire. Referenced library source and sink rules are collected and analyzed automatically.

The rule-id argument selects the one rule to trace. The optional source-path argument is the project root and defaults to the current directory. Pass --project-model to trace a pre-compiled model instead. The source-path argument and --project-model are mutually exclusive. Use --entry-points to start the analysis from a specific method.

The report is written as debug-ifds-fact-reachability.sarif next to the main SARIF report.

Run opentaint pull once before your first run to fetch the toolchain. Open the reachability report afterward with opentaint summary.

` + scanExitCodesHelp("Reachability analysis completed"),
	Example: `  # Trace a rule against the current directory
  opentaint test rule reachability <rule-id> .

  # Trace a rule against a pre-compiled project model
  opentaint test rule reachability <rule-id> --project-model ./model

  # Start the analysis from a specific entry-point method
  opentaint test rule reachability <rule-id> . --entry-points com.example.App#main

  # Validate inputs without compiling or scanning
  opentaint test rule reachability <rule-id> . --dry-run`,
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
