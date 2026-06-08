package cmd

import (
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
