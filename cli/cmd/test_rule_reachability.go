package cmd

import (
	"github.com/spf13/cobra"
)

var reachabilityEntryPoint string

var testRuleReachabilityCmd = &cobra.Command{
	Use:   "reachability <rule-id> [source-path]",
	Short: "Trace fact reachability for a single rule (why it does or does not fire)",
	Long: `This command scans the project for one rule and writes a sibling SARIF report with fact-reachability info to debug why the rule does or does not fire

Arguments:
  rule-id      - Full rule ID, e.g. security/SqlInjection.yaml:tainted-sql-from-http (required)
  source-path  - Path to the project sources (default: current directory)

The rule's library source/sink dependencies (its join refs) are collected and analyzed automatically.

The fact-reachability report is written next to the main SARIF as debug-ifds-fact-reachability.sarif.

Use --entry-points to seed the analysis at a specific method while tracing reachability:
  Non-Spring: RESTRICTS the entry-point set to this method only.
  Spring: ADDS this method to Spring's auto-discovered entry-point set (the set can't be narrowed on Spring).
The value is '*' for all methods or a method FQN like com.example.Class#method.

Use --project-model to scan a pre-compiled project model instead of compiling from sources.
`,
	Annotations: map[string]string{"PrintConfig": "true"},
	Args:        cobra.RangeArgs(1, 2),
	Run: func(cmd *cobra.Command, args []string) {
		RuleID = []string{args[0]}
		DebugFactReachabilitySarif = true
		expandRuleRefs = true
		if reachabilityEntryPoint != "" {
			out.Warn("on Spring projects this method is added to the auto-discovered entry points, not used to restrict them")
			DebugRunAnalysisOnSelectedEntryPoints = reachabilityEntryPoint
		}
		scanCmd.Run(scanCmd, args[1:])
	},
}

func init() {
	testRuleCmd.AddCommand(testRuleReachabilityCmd)
	addScanFlags(testRuleReachabilityCmd)
	testRuleReachabilityCmd.Flags().StringVar(&reachabilityEntryPoint, "entry-points", "",
		"Seed analysis at this method ('*' or FQN like com.example.Class#method); restricts on non-Spring, adds on Spring")
}
