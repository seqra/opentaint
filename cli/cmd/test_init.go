package cmd

import (
	"fmt"
	"path/filepath"

	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/testapprox"
	"github.com/seqra/opentaint/internal/testproject"
	"github.com/seqra/opentaint/internal/testrule"
	"github.com/spf13/cobra"
)

var initRuleProjectDeps []string
var initApproxProjectDeps []string
var initRuleSinksOnly bool
var initRuleSourcesOnly bool

var testRuleInitCmd = &cobra.Command{
	Use:   "init <output-dir>",
	Short: "Create rule test projects with source and sink harnesses",
	Long: `Create one or two Gradle test projects for detection-rule tests. The sinks project tests sink rules with a generic taint source. The sources project tests source rules with a generic taint sink.

The output-dir argument is the parent directory for the new projects. The default creates the two projects, in output-dir/sinks and output-dir/sources. To create one project only, use --sinks-only or --sources-only. To add compile-only Maven dependencies for the samples, use --dependency.

Each project contains a rule-test.yaml file and a Taint.java harness. Declare your positive and negative samples in rule-test.yaml.

Then compile the project with "opentaint compile" and run the samples with "opentaint test rule run".`,
	Example: `  # Create the sinks and the sources test projects
  opentaint test rule init ./rule-tests

  # Create only the sinks project
  opentaint test rule init ./rule-tests --sinks-only

  # Add a compile-only dependency for the samples
  opentaint test rule init ./rule-tests --dependency <group:artifact:version>

  # Recipe: from an empty directory to a first test run
  opentaint test rule init ./rule-tests
  opentaint compile ./rule-tests/sinks -o ./rule-tests/sinks/model
  opentaint test rule run ./rule-tests/sinks/model --ruleset ./my-rules`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		if initRuleSinksOnly && initRuleSourcesOnly {
			out.Fatalf("--sinks-only and --sources-only are mutually exclusive")
		}
		kinds := []string{"sinks", "sources"}
		if initRuleSinksOnly {
			kinds = []string{"sinks"}
		} else if initRuleSourcesOnly {
			kinds = []string{"sources"}
		}
		for _, kind := range kinds {
			dir := filepath.Join(args[0], kind)
			if err := testproject.Bootstrap(dir, "opentaint-rule-test-"+kind, initRuleProjectDeps); err != nil {
				out.Fatalf("Failed to bootstrap test project: %s", err)
			}
			if err := testrule.Scaffold(dir); err != nil {
				out.Fatalf("Failed to scaffold rule test project: %s", err)
			}
			out.Printf("Rule test project (%s) initialized at %s", kind, dir)
		}
		dir := filepath.Join(args[0], kinds[0])
		modelDir := filepath.Join(dir, "model")
		out.Suggestions(
			output.Suggestion{Description: "To add your test samples, edit:", Command: filepath.Join(dir, "rule-test.yaml")},
			output.Suggestion{Description: "To compile the test project, run:", Command: fmt.Sprintf("opentaint compile %s -o %s", dir, modelDir)},
			output.Suggestion{Description: "To run the tests, run:", Command: fmt.Sprintf("opentaint test rule run %s", modelDir)},
		)
	},
}

var testApproximationInitCmd = &cobra.Command{
	Use:   "init <output-dir>",
	Short: "Create a dataflow-approximation test project",
	Long: `Create a Gradle test project for dataflow-approximation tests. The project contains a fixed source-to-sink rule. The samples are checked against this rule.

The output-dir argument is the directory for the new project. To add compile-only Maven dependencies for the samples, use --dependency. The approximation under test is not part of the project. Give it at run time with --java-models.

The project contains a rule-test.yaml file, a Taint.java source and sink, and the fixed approximation-rule.yaml. Declare your positive and negative samples in rule-test.yaml.

Then compile the project with "opentaint compile" and run the samples with "opentaint test approximation run".`,
	Example: `  # Create an approximation test project
  opentaint test approximation init ./approx-test

  # Add a compile-only dependency for the samples
  opentaint test approximation init ./approx-test --dependency <group:artifact:version>

  # Recipe: from an empty directory to a first test run
  opentaint test approximation init ./approx-test
  opentaint compile ./approx-test -o ./approx-test/model
  opentaint test approximation run ./approx-test/model --java-models ./my-approximation`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		if err := testproject.Bootstrap(args[0], "approximation-test-project", initApproxProjectDeps); err != nil {
			out.Fatalf("Failed to bootstrap test project: %s", err)
		}
		if err := testapprox.Scaffold(args[0]); err != nil {
			out.Fatalf("Failed to scaffold approximation project: %s", err)
		}
		out.Printf("Approximation test project initialized at %s", args[0])
		dir := args[0]
		modelDir := filepath.Join(dir, "model")
		out.Suggestions(
			output.Suggestion{Description: "To add your test samples, edit:", Command: filepath.Join(dir, "rule-test.yaml")},
			output.Suggestion{Description: "To compile the test project, run:", Command: fmt.Sprintf("opentaint compile %s -o %s", dir, modelDir)},
			output.Suggestion{Description: "To run the tests, run:", Command: fmt.Sprintf("opentaint test approximation run %s --java-models <approximation>", modelDir)},
		)
	},
}

func init() {
	testRuleCmd.AddCommand(testRuleInitCmd)
	testRuleInitCmd.Flags().StringArrayVar(&initRuleProjectDeps, "dependency", nil,
		"Compile-only Maven dependency coordinates for generated samples (repeatable)")
	testRuleInitCmd.Flags().BoolVar(&initRuleSinksOnly, "sinks-only", false,
		"Create only the sinks test project")
	testRuleInitCmd.Flags().BoolVar(&initRuleSourcesOnly, "sources-only", false,
		"Create only the sources test project")

	testApproximationCmd.AddCommand(testApproximationInitCmd)
	testApproximationInitCmd.Flags().StringArrayVar(&initApproxProjectDeps, "dependency", nil,
		"Compile-only Maven dependency coordinates for generated samples (repeatable)")
}
