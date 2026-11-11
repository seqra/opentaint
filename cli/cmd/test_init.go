package cmd

import (
	"fmt"

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
		suggestions := []output.Suggestion{
			{Description: "To learn more about the test projects, see:", Command: usageDocsURL + "#rule-tests"},
		}
		for _, kind := range kinds {
			dir := joinUserPath(args[0], kind)
			existing := testproject.Exists(dir)
			warnReplacingBuildFile(existing, dir)
			if err := testproject.Bootstrap(dir, "opentaint-rule-test-"+kind, initRuleProjectDeps); err != nil {
				out.Fatal("Failed to create the test project", err)
			}
			if err := testrule.Scaffold(dir); err != nil {
				out.Fatal("Failed to create the test samples", err)
			}
			printInitResult(existing, "the "+kind+" test project", dir)

			goal := "To run the tests after you add the samples, first run:"
			if len(kinds) > 1 {
				goal = fmt.Sprintf("To run the %s tests after you add the samples, first run:", kind)
			}
			suggestions = append(suggestions, output.Suggestion{Description: goal, Command: "opentaint compile " + shellQuote(dir)})
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
		dir := args[0]
		existing := testproject.Exists(dir)
		warnReplacingBuildFile(existing, dir)
		if err := testproject.Bootstrap(dir, "model-test-project", initModelProjectDeps); err != nil {
			out.Fatal("Failed to create the test project", err)
		}
		if err := testmodel.Scaffold(dir); err != nil {
			out.Fatal("Failed to create the test samples", err)
		}
		printInitResult(existing, "the model test project", dir)
		out.Suggestions(
			output.Suggestion{Description: "To learn more about the test projects, see:", Command: usageDocsURL + "#model-tests"},
			output.Suggestion{Description: "To run the tests after you add the samples, first run:", Command: "opentaint compile " + shellQuote(dir)},
		)
	},
}

// warnReplacingBuildFile warns, when init runs on an existing project, that the build file is
// replaced: the dependencies that it had and that --dependency does not repeat are gone. Init
// keeps the files of the user, such as the models, the samples, and rule-test.yaml.
func warnReplacingBuildFile(existing bool, dir string) {
	if existing {
		out.WarnDetails(fmt.Sprintf("Replacing the build file of `%s`", dir),
			"the new build file has only the libraries from --dependency")
	}
}

// printInitResult prints what init did with the project at dir.
func printInitResult(existing bool, project, dir string) {
	if existing {
		out.Successf("Updated %s at `%s`", project, dir)
		return
	}
	out.Successf("Created %s at `%s`", project, dir)
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
