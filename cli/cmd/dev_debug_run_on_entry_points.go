package cmd

import (
	"github.com/spf13/cobra"
)

var devDebugRunOnEntryPointsCmd = &cobra.Command{
	Use:   "debug-run-on-entry-points <entry-point> [source-path]",
	Short: "Run analysis on selected entry points",
	Args:  cobra.RangeArgs(1, 2),
	Long: `This command scans the project starting only from the given entry point, useful for narrowing analysis while debugging a rule

Arguments:
  entry-point  - '*' for all methods or method FQN like com.example.Class#method (required)
  source-path  - Path to the project sources (default: current directory)

Note: this command is ignored on Spring projects

Use --project-model to scan a pre-compiled project model instead of compiling from sources.
`,
	Annotations: map[string]string{"PrintConfig": "true"},
	Run: func(cmd *cobra.Command, args []string) {
		out.Warn("entry-point override has no effect on Spring projects")
		DebugRunAnalysisOnSelectedEntryPoints = args[0]
		scanCmd.Run(scanCmd, args[1:])
	},
}

func init() {
	devCmd.AddCommand(devDebugRunOnEntryPointsCmd)
	addScanFlags(devDebugRunOnEntryPointsCmd)
	addRuleIDFlag(devDebugRunOnEntryPointsCmd)
}
