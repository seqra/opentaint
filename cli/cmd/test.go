package cmd

import (
	"time"

	"github.com/spf13/cobra"
)

var testCmd = &cobra.Command{
	Use:   "test",
	Short: "Create and run rule and approximation tests",
	Long: `Create, run, and debug rule and approximation tests. Rule tests check detection rules against annotated sample projects; approximation tests check dataflow approximations the same way.

Scaffold a project with init, compile it with opentaint compile, then run the samples with test rule run or test approximation run. Use test rule reachability to debug why a single rule does or does not fire.`,
}

var testRuleCmd = &cobra.Command{
	Use:   "rule",
	Short: "Create, run, and debug detection-rule tests",
	Long: `Create, run, and debug taint detection-rule tests. Rule tests check that a rule fires on positive samples and stays silent on negative ones.

Scaffold a test project with test rule init, compile it with opentaint compile, then run the samples with test rule run. Use test rule reachability to trace why a single rule does or does not fire.`,
}

var testApproximationCmd = &cobra.Command{
	Use:   "approximation",
	Short: "Create and run dataflow-approximation tests",
	Long: `Create and run dataflow-approximation tests. Approximation tests check that a dataflow approximation carries taint from source to sink across your samples.

Scaffold a test project with test approximation init, compile it with opentaint compile, then run the samples with test approximation run, supplying the approximation under test with --java-models.`,
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
	cmd.Flags().StringArrayVar(dataflow, "java-models", nil, "Java dataflow models: a compiled class directory or a Java source directory (repeatable)")
	cmd.Flags().StringArrayVar(dataflow, "dataflow-approximations", nil, "Java dataflow models: a compiled class directory or a Java source directory (repeatable)")
	_ = cmd.Flags().MarkDeprecated("dataflow-approximations", "use --java-models")
}
