package cmd

import (
	"github.com/spf13/cobra"
)

var devDebugFactReachabilityCmd = &cobra.Command{
	Use:   "debug-fact-reachability <rule-id> [source-path]",
	Short: "Generate SARIF with fact reachability info for a single rule",
	Args:  cobra.RangeArgs(1, 2),
	Long: `This command scans the project for one rule and writes a sibling SARIF report with fact-reachability info to debug why the rule does or does not fire

Arguments:
  rule-id      - Full rule ID, e.g. security/SqlInjection.yaml:tainted-sql-from-http (required)
  source-path  - Path to the project sources (default: current directory)

The fact-reachability report is written next to the main SARIF as debug-ifds-fact-reachability.sarif.

Use --project-model to scan a pre-compiled project model instead of compiling from sources.
`,
	Annotations: map[string]string{"PrintConfig": "true"},
	Run: func(cmd *cobra.Command, args []string) {
		RuleID = []string{args[0]}
		DebugFactReachabilitySarif = true
		scanCmd.Run(scanCmd, args[1:])
	},
}

func init() {
	devCmd.AddCommand(devDebugFactReachabilityCmd)
	addScanFlags(devDebugFactReachabilityCmd)
}
