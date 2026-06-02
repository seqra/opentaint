package cmd

import (
	"github.com/spf13/cobra"
)

// testCmd groups the rule/approximation authoring, testing, and debugging tools (experimental).
var testCmd = &cobra.Command{
	Use:   "test",
	Short: "Author, test, and debug rules and approximations (experimental)",
	Long:  `Utilities for the rule and approximation test-driven loop: scaffold a test project, run tests against annotated samples, and trace fact reachability when a rule misbehaves (experimental)`,
}

// testRuleCmd groups the rule-authoring subcommands (init/run/reachability).
var testRuleCmd = &cobra.Command{
	Use:   "rule",
	Short: "Scaffold, test, and debug detection rules",
}

// testApproximationCmd groups the approximation-authoring subcommands (init/run).
var testApproximationCmd = &cobra.Command{
	Use:   "approximation",
	Short: "Scaffold and test dataflow approximations",
}

func init() {
	rootCmd.AddCommand(testCmd)
	testCmd.AddCommand(testRuleCmd)
	testCmd.AddCommand(testApproximationCmd)
}
