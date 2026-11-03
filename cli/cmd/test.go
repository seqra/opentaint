package cmd

import (
	"time"

	"github.com/spf13/cobra"
)

var testCmd = &cobra.Command{
	Use:   "test",
	Short: "Create and run rule and model tests",
}

var testRuleCmd = &cobra.Command{
	Use:   "rule",
	Short: "Create, run, and debug rule tests",
}

var testModelCmd = &cobra.Command{
	Use:   "model",
	Short: "Create and run dataflow model tests",
}

// testApproximationCmd is the deprecated name of testModelCmd.
var testApproximationCmd = deprecatedGroup(testModelCmd, "opentaint test approximation", "opentaint test model")

func init() {
	rootCmd.AddCommand(testCmd)
	testCmd.AddCommand(testRuleCmd)
	testCmd.AddCommand(testModelCmd)
	testCmd.AddCommand(testApproximationCmd)
}

func addTestRunFlags(cmd *cobra.Command, outputDir *string, timeout *time.Duration, maxMemory *string, dataflow, passthrough *[]string) {
	cmd.Flags().StringVarP(outputDir, "output", "o", "", "Directory for test-result.json and test-results.sarif (default: a temporary directory)")
	cmd.Flags().DurationVar(timeout, "timeout", 600*time.Second, "Analysis timeout (e.g. 30m, 1h)")
	cmd.Flags().StringVar(maxMemory, "max-memory", "8G", "Maximum analyzer heap size (e.g. 8G, 1024m)")
	addDataflowModelsFlag(cmd, dataflow)
	addPassthroughModelsFlag(cmd, passthrough)
}
