package cmd

import (
	"time"

	"github.com/spf13/cobra"
)

// testCmd groups the rule/approximation authoring, testing, and debugging tools (experimental).
var testCmd = &cobra.Command{
	Use:   "test",
	Short: "Create and run rule and approximation tests (experimental)",
	Long:  `Experimental tools for creating test projects, running annotated rule and approximation tests, and debugging rule reachability.`,
}

// testRuleCmd groups the rule-authoring subcommands (init/run/reachability).
var testRuleCmd = &cobra.Command{
	Use:   "rule",
	Short: "Create, run, and debug detection-rule tests",
}

// testApproximationCmd groups the approximation-authoring subcommands (init/run).
var testApproximationCmd = &cobra.Command{
	Use:   "approximation",
	Short: "Create and run dataflow-approximation tests",
}

func init() {
	rootCmd.AddCommand(testCmd)
	testCmd.AddCommand(testRuleCmd)
	testCmd.AddCommand(testApproximationCmd)
}

// testExitCodesHelp documents the exit codes shared by `test rule run` and
// `test approximation run`. Codes 252-255 mirror internal/analyzer.
func testExitCodesHelp(passedLine string) string {
	return `Exit codes:
  0    ` + passedLine + `
  1    General failure (configuration or infrastructure error)
  2    One or more tests failed (false negatives/positives or skipped samples)
  252  Unhandled analyzer exception
  253  Out of memory (try increasing --max-memory)
  254  Analysis timed out (try increasing --timeout)
  255  Project configuration error`
}

// addTestRunFlags registers the flags shared by `test rule run` and
// `test approximation run`.
func addTestRunFlags(cmd *cobra.Command, outputDir *string, timeout *time.Duration, maxMemory *string, dataflow *[]string) {
	cmd.Flags().StringVarP(outputDir, "output", "o", "", "Directory for test-result.json and test-results.sarif")
	cmd.Flags().DurationVar(timeout, "timeout", 600*time.Second, "Analysis timeout")
	cmd.Flags().StringVar(maxMemory, "max-memory", "8G", "Maximum analyzer heap size (e.g., 8G)")
	cmd.Flags().StringArrayVar(dataflow, "dataflow-approximations", nil, "Dataflow approximation class directory or Java source directory (repeatable)")
}
