package cmd

import (
	"github.com/spf13/cobra"
)

var reachabilityEntryPoint string

var testRuleReachabilityCmd = &cobra.Command{
	Use:   "reachability <rule-id> [source-path]",
	Short: "Trace why a rule can or cannot reach its facts",
	Long: `Scan a project with one rule and write a sibling SARIF report with
fact-reachability details. Use this to debug why a rule does or does not fire.

Arguments:
  rule-id      - Full rule ID, e.g. security/sqli.yaml:sql-injection
  source-path  - Path to the project sources (default: current directory)

Referenced library source and sink rules are collected and analyzed automatically.

The fact-reachability report is written next to the main SARIF as debug-ifds-fact-reachability.sarif.

Use --entry-points to start analysis from a specific method while tracing reachability.
The value is '*' for all methods or a fully qualified method such as com.example.Class#method.
For non-Spring projects this restricts the entry-point set. For Spring projects it adds to
the auto-discovered entry points because Spring entry points cannot be narrowed.

Use --project-model to scan a pre-compiled project model instead of compiling from sources.
`,
	Annotations: map[string]string{"PrintConfig": "true"},
	Args:        cobra.RangeArgs(1, 2),
	Run: func(cmd *cobra.Command, args []string) {
		// `reachability` is `scan` with a forced preset. It shares the scan
		// flags (so scanFlags carries the parsed --ruleset, --output, ... ) but
		// builds an explicit ScanConfig with the reachability overrides applied
		// instead of mutating shared state, then runs the same scan pipeline.
		if reachabilityEntryPoint != "" {
			out.Warn("on Spring projects this method is added to the auto-discovered entry points, not used to restrict them")
		}
		cfg := reachabilityScanConfig(scanFlags, args[0], reachabilityEntryPoint)
		runScan(cmd, prepareScanConfig(cfg, args[1:]))
	},
}

// reachabilityScanConfig returns the scan config for a `test rule reachability`
// run: the base scan flags with the reachability-specific presets applied
// (single rule, fact-reachability SARIF, rule-ref expansion, optional
// entry-point restriction).
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
		"Start from '*' or a fully qualified method such as com.example.Class#method")
}
