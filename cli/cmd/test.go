package cmd

import (
	"time"

	"github.com/spf13/cobra"
)

var testCmd = &cobra.Command{
	Use:   "test",
	Short: "Create and run rule and model tests",
	Long:  `Tools for creating test projects, running annotated rule and model tests, and debugging rule reachability.`,
}

var testRuleCmd = &cobra.Command{
	Use:   "rule",
	Short: "Create, run, and debug detection-rule tests",
}

var testModelCmd = &cobra.Command{
	Use:   "model",
	Short: "Create and run dataflow model tests",
}

// testApproximationCmd is the deprecated name of testModelCmd.
var testApproximationCmd = &cobra.Command{
	Use:        "approximation",
	Short:      testModelCmd.Short,
	Deprecated: "use 'opentaint test model' instead",
}

func init() {
	rootCmd.AddCommand(testCmd)
	testCmd.AddCommand(testRuleCmd)
	testCmd.AddCommand(testModelCmd)
	testCmd.AddCommand(testApproximationCmd)
}

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

func addTestRunFlags(
	cmd *cobra.Command,
	outputDir *string,
	timeout *time.Duration,
	maxMemory *string,
	dataflow *[]string,
) {
	cmd.Flags().StringVarP(outputDir, "output", "o", "", "Directory for test-result.json and test-results.sarif")
	cmd.Flags().DurationVar(timeout, "timeout", 600*time.Second, "Analysis timeout")
	cmd.Flags().StringVar(maxMemory, "max-memory", "8G", "Maximum analyzer heap size (e.g., 8G)")
	addDataflowModelsFlag(cmd, dataflow)
}
