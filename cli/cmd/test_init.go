package cmd

import (
	"fmt"
	"path/filepath"

	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/testmodel"
	"github.com/seqra/opentaint/internal/testproject"
	"github.com/seqra/opentaint/internal/testrule"
	"github.com/spf13/cobra"
)

var initRuleProjectDeps []string
var initModelProjectDeps []string
var initRuleSinksOnly bool
var initRuleSourcesOnly bool

var testRuleInitCmd = &cobra.Command{
	Use:   "init <output-dir>",
	Short: "Create rule test projects with source and sink harnesses",
	Long: `Create Gradle test projects for detection rules. The sinks project tests sink rules against a generic taint source, and the sources project tests source rules against a generic taint sink

Arguments:
  <output-dir>  Parent directory of the sinks and sources projects

Declare the positive and negative samples in the rule-test.yaml file of each project`,
	Example: `  # Create only the sinks project, with a library that the samples call
  opentaint test rule init ./rule-tests --sinks-only --dependency org.springframework:spring-jdbc:6.1.14`,
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
		var suggestions []output.Suggestion
		for _, kind := range kinds {
			dir := filepath.Join(args[0], kind)
			modelDir := filepath.Join(dir, "model")
			suggestions = append(suggestions,
				output.Suggestion{Description: fmt.Sprintf("To add %s test samples, edit:", kind), Command: filepath.Join(dir, "rule-test.yaml")},
				output.Suggestion{Description: fmt.Sprintf("To compile the %s test project, run:", kind), Command: fmt.Sprintf("opentaint compile %s -o %s", shellQuote(dir), shellQuote(modelDir))},
				output.Suggestion{Description: fmt.Sprintf("To run the %s tests, run:", kind), Command: fmt.Sprintf("opentaint test rule run %s", shellQuote(modelDir))},
			)
		}
		out.Suggestions(suggestions...)
	},
}

var testModelInitCmd = &cobra.Command{
	Use:   "init <output-dir>",
	Short: "Create a dataflow model test project",
	Long: `Create a Gradle test project for dataflow models. A sample passes taint from Taint.source() through the modeled method to Taint.sink(), and the fixed rule model-rule checks that the taint reaches the sink

Arguments:
  <output-dir>  Directory of the new test project

Declare the positive and negative samples in rule-test.yaml. The model under test is given to "opentaint test model run" with --dataflow-models`,
	Example: `  # Create a test project whose samples call jackson-databind
  opentaint test model init ./model-test --dependency com.fasterxml.jackson.core:jackson-databind:2.17.2`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		if err := testproject.Bootstrap(args[0], "model-test-project", initModelProjectDeps); err != nil {
			out.Fatalf("Failed to bootstrap test project: %s", err)
		}
		if err := testmodel.Scaffold(args[0]); err != nil {
			out.Fatalf("Failed to scaffold model test project: %s", err)
		}
		out.Printf("Model test project initialized at %s", args[0])
		dir := args[0]
		modelDir := filepath.Join(dir, "model")
		out.Suggestions(
			output.Suggestion{Description: "To add your test samples, edit:", Command: filepath.Join(dir, "rule-test.yaml")},
			output.Suggestion{Description: "To compile the test project, run:", Command: fmt.Sprintf("opentaint compile %s -o %s", shellQuote(dir), shellQuote(modelDir))},
			output.Suggestion{Description: "To run the tests, run:", Command: fmt.Sprintf("opentaint test model run %s --dataflow-models <model>", shellQuote(modelDir))},
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

	testModelCmd.AddCommand(testModelInitCmd)
	testModelInitCmd.Flags().StringArrayVar(&initModelProjectDeps, "dependency", nil,
		"Compile-only Maven dependency coordinates for generated samples (repeatable)")
	testApproximationCmd.AddCommand(deprecatedCommand(testModelInitCmd, "init", "opentaint test model init"))
}
