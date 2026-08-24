package cmd

import (
	"github.com/spf13/cobra"
)

var reachabilityEntryPoint string

var testRuleReachabilityCmd = &cobra.Command{
	Use:   "reachability <rule-id> [source-path]",
	Short: "Show why a rule does or does not fire",
	Long: `Scan a project with one rule and write a fact-reachability SARIF report. The report shows why the rule does or does not fire. Library source and sink rules that the rule points to are included automatically.

The rule-id argument selects the rule. The source-path argument is the project root. It is optional. The default is the current directory. To use a compiled model, use --project-model. Do not give source-path and --project-model together. To start the analysis from one method, use --entry-points.

The report name is debug-ifds-fact-reachability.sarif. It is written adjacent to the main SARIF report.

Before the first run, run "opentaint pull" one time. To read the report, use "opentaint summary".

` + scanExitCodesHelp("Reachability analysis completed"),
	Example: `  # Show why a rule does or does not fire on the current directory
  opentaint test rule reachability <rule-id> .

  # Examine a rule on a compiled project model
  opentaint test rule reachability <rule-id> --project-model ./model

  # Start the analysis from one entry-point method
  opentaint test rule reachability <rule-id> . --entry-points com.example.App#main

  # Make sure the inputs are correct, without a scan
  opentaint test rule reachability <rule-id> . --dry-run

  # Recipe: find why a new rule stays silent
  opentaint test rule reachability <rule-id> . -o report.sarif
  opentaint summary debug-ifds-fact-reachability.sarif --show-findings --verbose-flow`,
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
