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
	Short: "Create test projects for sink and source rules",
	Long:  "Create test projects for sink and source rules.\n\nArguments:\n  <output-dir>  Parent directory of the `sinks` and `sources` projects",
	Example: `  # Create only the sinks project, with a library that the samples call
  opentaint test rule init .opentaint/test-projects/my-rule --sinks-only \
    --dependency org.springframework:spring-jdbc:6.1.14`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		if initRuleSinksOnly && initRuleSourcesOnly {
			out.Fatalf("Cannot use --sinks-only with --sources-only")
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
				out.Fatal("Failed to create the test project", err)
			}
			if err := testrule.Scaffold(dir); err != nil {
				out.Fatal("Failed to create the test samples", err)
			}
			out.Printf("Rule test project (%s) initialized at `%s`", kind, dir)
		}
		var suggestions []output.Suggestion
		for _, kind := range kinds {
			dir := filepath.Join(args[0], kind)
			modelDir := filepath.Join(dir, "model")
			suggestions = append(suggestions,
				output.Suggestion{Description: fmt.Sprintf("To add %s test samples, edit:", kind), Command: filepath.Join(dir, testproject.RuleTestFileName)},
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
	Long:  "Create a dataflow model test project.\n\nArguments:\n  <output-dir>  Directory of the new test project",
	Example: `  # Create a test project with samples that call Jackson
  opentaint test model init .opentaint/test-projects/my-model \
    --dependency com.fasterxml.jackson.core:jackson-databind:2.17.2`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		if err := testproject.Bootstrap(args[0], "model-test-project", initModelProjectDeps); err != nil {
			out.Fatal("Failed to create the test project", err)
		}
		if err := testmodel.Scaffold(args[0]); err != nil {
			out.Fatal("Failed to create the test samples", err)
		}
		out.Printf("Model test project initialized at `%s`", args[0])
		dir := args[0]
		modelDir := filepath.Join(dir, "model")
		out.Suggestions(
			output.Suggestion{Description: "To add your test samples, edit:", Command: filepath.Join(dir, testproject.RuleTestFileName)},
			output.Suggestion{Description: "To compile the test project, run:", Command: fmt.Sprintf("opentaint compile %s -o %s", shellQuote(dir), shellQuote(modelDir))},
			output.Suggestion{Description: "To run the tests, run:", Command: fmt.Sprintf("opentaint test model run %s --dataflow-models <model-project>", shellQuote(modelDir))},
		)
	},
}

func init() {
	testRuleCmd.AddCommand(testRuleInitCmd)
	testRuleInitCmd.Flags().StringArrayVar(&initRuleProjectDeps, "dependency", nil,
		"Library that the samples call, as group:artifact:version (repeatable)")
	testRuleInitCmd.Flags().BoolVar(&initRuleSinksOnly, "sinks-only", false,
		"Create only the sinks project")
	testRuleInitCmd.Flags().BoolVar(&initRuleSourcesOnly, "sources-only", false,
		"Create only the sources project")

	testModelCmd.AddCommand(testModelInitCmd)
	testModelInitCmd.Flags().StringArrayVar(&initModelProjectDeps, "dependency", nil,
		"Library that the samples call, as group:artifact:version (repeatable)")
	testApproximationCmd.AddCommand(deprecatedCommand(testModelInitCmd, "opentaint test approximation init", "opentaint test model init"))
}
