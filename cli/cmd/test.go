package cmd

import (
	"time"

	"github.com/spf13/cobra"
)

var testCmd = &cobra.Command{
	Use:   "test",
	Short: "Create and run rule and model tests",
	Long: `Create and run tests for detection rules and dataflow models. Rule tests make sure that a rule finds the positive samples and ignores the negative samples. Dataflow model tests make sure that a model moves taint from source to sink.

Workflow:
  1. Create a test project with init.
  2. Compile the project with "opentaint compile".
  3. Run the samples with "test rule run" or "test dataflow-model run".

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

var testModelCmd = &cobra.Command{
	Use:     "dataflow-model",
	Aliases: []string{"approximation"},
	Short:   "Create and run dataflow model tests",
	PersistentPreRun: func(cmd *cobra.Command, args []string) {
		if cmd.Parent().CalledAs() == "approximation" {
			out.Warnf("command 'test approximation' is deprecated; use 'test dataflow-model' instead")
		}
	},
	Long: `Create and run tests for dataflow models. A model test makes sure that a model moves taint from source to sink in your samples.

Workflow:
  1. Create a test project with "test dataflow-model init".
  2. Compile the project with "opentaint compile".
  3. Run the samples with "test dataflow-model run --java-models <model>".`,
}

func init() {
	rootCmd.AddCommand(testCmd)
	testCmd.AddCommand(testRuleCmd)
	testCmd.AddCommand(testModelCmd)
}

func addTestRunFlags(cmd *cobra.Command, outputDir *string, timeout *time.Duration, maxMemory *string, dataflow *[]string) {
	cmd.Flags().StringVarP(outputDir, "output", "o", "", "Directory for test-result.json and test-results.sarif")
	cmd.Flags().DurationVar(timeout, "timeout", 600*time.Second, "Maximum wall-clock time for analysis (e.g. 30m, 1h)")
	cmd.Flags().StringVar(maxMemory, "max-memory", "8G", "Maximum analyzer heap size (e.g. 8G, 1024m)")
	addRenamedStringArrayFlag(cmd.Flags(), dataflow, "java-models", "dataflow-approximations", "Java dataflow models: a model project, build output, or class directory (repeatable)")
}
