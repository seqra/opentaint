package cmd

import (
	"github.com/spf13/cobra"
)

var reachabilityEntryPoint string

var testRuleReachabilityCmd = &cobra.Command{
	Use:   "reachability <rule-id> [source-path]",
	Short: "Show why a rule does or does not fire",
	Long: `Scan a project with one rule and write a fact-reachability report that shows why the rule does or does not fire. The library source and sink rules that the rule refers to are included

Arguments:
  <rule-id>      Full ID of the rule, such as java/security/path-traversal.yaml:path-traversal
  [source-path]  Root directory of the project (default: the current directory)

To use a compiled project model, give --project-model instead of [source-path]. The report debug-ifds-fact-reachability.sarif is written next to the SARIF report

` + scanExitCodesHelp("Reachability analysis completed"),
	Example: `  # Debug the path-traversal rule from one entry point
  opentaint test rule reachability java/security/path-traversal.yaml:path-traversal ./app \
    --entry-points com.example.FileController#download`,
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
	testRuleReachabilityCmd.Flags().StringVar(&reachabilityEntryPoint, "entry-points", "", entryPointsUsage)
}
