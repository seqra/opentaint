package cmd

import (
	"time"

	"github.com/spf13/cobra"
)

var testCmd = &cobra.Command{
	Use:   "test",
	Short: "Create and run rule and approximation tests",
	Long: `Create and run tests for detection rules and for dataflow approximations. Rule tests make sure that a rule finds the positive samples and ignores the negative samples. Approximation tests make sure that a dataflow approximation moves taint from source to sink.

Workflow:
  1. Create a test project with init.
  2. Compile the project with "opentaint compile".
  3. Run the samples with "test rule run" or "test approximation run".

To see why one rule does or does not fire, use "test rule reachability".`,
}

var testRuleCmd = &cobra.Command{
	Use:   "rule",
	Short: "Create, run, and debug detection-rule tests",
	Long: `Create, run, and debug tests for taint detection rules. A rule test makes sure that a rule finds the positive samples and ignores the negative samples.

Workflow:
  1. Create a test project with "test rule init".
  2. Compile the project with "opentaint compile".
  3. Run the samples with "test rule run".

To see why one rule does or does not fire, use "test rule reachability".`,
}

var testApproximationCmd = &cobra.Command{
	Use:   "approximation",
	Short: "Create and run dataflow-approximation tests",
	Long: `Create and run tests for dataflow approximations. An approximation test makes sure that an approximation moves taint from source to sink in your samples.

Workflow:
  1. Create a test project with "test approximation init".
  2. Compile the project with "opentaint compile".
  3. Run the samples with "test approximation run --java-models <approximation>".`,
}

func init() {
	rootCmd.AddCommand(testCmd)
	testCmd.AddCommand(testRuleCmd)
	testCmd.AddCommand(testApproximationCmd)
}

func addTestRunFlags(cmd *cobra.Command, outputDir *string, timeout *time.Duration, maxMemory *string, dataflow *[]string) {
	cmd.Flags().StringVarP(outputDir, "output", "o", "", "Directory for test-result.json and test-results.sarif")
	cmd.Flags().DurationVar(timeout, "timeout", 600*time.Second, "Maximum wall-clock time for analysis (e.g. 30m, 1h)")
	cmd.Flags().StringVar(maxMemory, "max-memory", "8G", "Maximum analyzer heap size (e.g. 8G, 1024m)")
	addRenamedStringArrayFlag(cmd.Flags(), dataflow, "java-models", "dataflow-approximations", "Java dataflow models: a compiled class directory or a Java source directory (repeatable)")
}
