package cmd

import (
	"time"

	"github.com/spf13/cobra"
)

var testCmd = &cobra.Command{
	Use:   "test",
	Short: "Create and run rule and model tests",
	Long: `Create and run tests of detection rules and dataflow models. A test project declares positive samples, which must produce a finding, and negative samples, which must not

Workflow:
  1. Create a test project with "test rule init" or "test model init"
  2. Write the samples and declare them in rule-test.yaml
  3. Compile the test project with "opentaint compile"
  4. Run the samples with "test rule run" or "test model run"`,
}

var testRuleCmd = &cobra.Command{
	Use:   "rule",
	Short: "Create, run, and debug rule tests",
	Long:  `Create and run tests of detection rules. To see why a rule does or does not fire on a project, use "test rule reachability"`,
}

var testModelCmd = &cobra.Command{
	Use:   "model",
	Short: "Create and run dataflow model tests",
	Long:  `Create and run tests of dataflow models. A model test checks that a model passes taint from source to sink`,
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

func addTestRunFlags(cmd *cobra.Command, outputDir *string, timeout *time.Duration, maxMemory *string, dataflow, passthrough *[]string) {
	cmd.Flags().StringVarP(outputDir, "output", "o", "", "Directory for test-result.json and test-results.sarif (default: a temporary directory)")
	cmd.Flags().DurationVar(timeout, "timeout", 600*time.Second, "Analysis timeout (e.g. 30m, 1h)")
	cmd.Flags().StringVar(maxMemory, "max-memory", "8G", "Maximum analyzer heap size (e.g. 8G, 1024m)")
	addDataflowModelsFlag(cmd, dataflow)
	addPassthroughModelsFlag(cmd, passthrough)
}
