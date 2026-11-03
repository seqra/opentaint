package cmd

import (
	"github.com/spf13/cobra"
)

var reachabilityEntryPoint string

var testRuleReachabilityCmd = &cobra.Command{
	Use:   "reachability <rule-id> [<source-path>]",
	Short: "Show why a rule does or does not fire",
	Long:  "Show why a rule does or does not fire on a project.\n\nArguments:\n  <rule-id>        Full rule ID, e.g. java/security/sqli.yaml:sql-injection\n  [<source-path>]  Project root (default: the current directory)",
	Example: `  # Show why a rule does not fire on the project in the current directory
  opentaint test rule reachability java/security/sqli.yaml:sql-injection .

  # Trace a rule from one entry point
  opentaint test rule reachability \
    java/security/path-traversal.yaml:path-traversal . \
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
