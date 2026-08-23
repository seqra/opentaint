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
	Long: `Create one or two Gradle test projects for detection-rule tests. The sinks project tests sink rules against a generic taint source; the sources project tests source rules against a generic taint sink.

The output-dir argument is the parent directory the projects are created under. By default both are scaffolded, as output-dir/sinks and output-dir/sources; pass --sinks-only or --sources-only to create just one. Use --dependency to add compile-only Maven dependencies for the samples.

Each project ships a rule-test.yaml where you declare the positive and negative samples, plus a Taint.java source and sink harness.

After editing rule-test.yaml, compile the project with opentaint compile and run the samples with opentaint test rule run.`,
	Example: `  # Scaffold both the sinks and sources test projects
  opentaint test rule init ./rule-tests

  # Scaffold only the sinks project
  opentaint test rule init ./rule-tests --sinks-only

  # Add a compile-only dependency for the samples
  opentaint test rule init ./rule-tests --dependency <group:artifact:version>`,
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
	Long: `Create a Gradle test project for dataflow-approximation tests. The project pins a fixed source-to-sink rule that the samples are checked against.

The output-dir argument is the directory the project is created in. Use --dependency to add compile-only Maven dependencies for the samples. The approximation under test is not baked in; supply it at run time with --dataflow-approximations.

The project ships a rule-test.yaml where you declare the positive and negative samples, plus a Taint.java source and sink and the fixed approximation-rule.yaml.

After editing rule-test.yaml, compile the project with opentaint compile and run the samples with opentaint test approximation run.`,
	Example: `  # Scaffold an approximation test project
  opentaint test approximation init ./approx-test

  # Add a compile-only dependency for the samples
  opentaint test approximation init ./approx-test --dependency <group:artifact:version>`,
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
			output.Suggestion{Description: "To run the tests, run:", Command: fmt.Sprintf("opentaint test approximation run %s --dataflow-approximations <approximation>", modelDir)},
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
