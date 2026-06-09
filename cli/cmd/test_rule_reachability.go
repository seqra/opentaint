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
		// `reachability` is `scan` with a forced flag preset. scan reads its
		// inputs from package-level vars (bound to its cobra flags), so we set
		// those vars here and delegate to scanCmd.Run rather than duplicating
		// the scan pipeline. This relies on shared mutable state: it assumes a
		// single, non-concurrent command invocation per process (the CLI
		// contract), and any new scan input must be wired through the same vars.
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
		"Start from '*' or a fully qualified method such as com.example.Class#method")
}
