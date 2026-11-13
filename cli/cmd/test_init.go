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
var initRuleLanguage string
var initModelTestLanguage string

// goTestModulePath is the module path of a Go test project. The samples are in its root package,
// so rule-test.yaml names them test.<function>.
const goTestModulePath = "test"

var testRuleInitCmd = &cobra.Command{
	Use:   "init <test-project>",
	Short: "Create test projects for sink and source rules",
	Long:  "Create test projects for sink and source rules.\n\nArguments:\n  <test-project>  Directory of the new sinks and sources test projects",
	Example: `  # Create only the sinks project, with a library that the samples call
  opentaint test rule init .opentaint/test-projects/my-rule --language java --sinks-only \
    --dependency org.springframework:spring-jdbc:5.3.39

  # Create only the sinks project for Go samples that call Gin
  opentaint test rule init .opentaint/test-projects/my-rule --language go --sinks-only \
    --dependency github.com/gin-gonic/gin@v1.10.0`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		if initRuleSinksOnly && initRuleSourcesOnly {
			out.Fatalf("Cannot use --sinks-only with --sources-only")
		}
		language := parseLanguage(initRuleLanguage)
		kinds := []string{"sinks", "sources"}
		if initRuleSinksOnly {
			kinds = []string{"sinks"}
		} else if initRuleSourcesOnly {
			kinds = []string{"sources"}
		}
		for _, kind := range kinds {
			dir := joinUserPath(args[0], kind)
			existing := checkTestProjectLanguage(dir, language)
			var err error
			if language == "go" {
				err = testproject.BootstrapGo(dir, goTestModulePath, initRuleProjectDeps)
			} else {
				err = testproject.Bootstrap(dir, "opentaint-rule-test-"+kind, initRuleProjectDeps)
			}
			if err != nil {
				out.Fatal("Failed to create the test project", err)
			}
			if language == "go" {
				err = testrule.ScaffoldGo(dir)
			} else {
				err = testrule.Scaffold(dir)
			}
			if err != nil {
				out.Fatal("Failed to create the test samples", err)
			}
			printInitResult(existing, "the "+kind+" test project", dir)
		}

		compile := output.Suggestion{
			Description: "To run the tests after you add the samples, first run:",
			Command:     testCompileCommand(args[0], kinds[0]),
		}
		if len(kinds) > 1 {
			compile = output.Suggestion{
				Description: "To run the sinks or sources tests after you add the samples, first run:",
				Command:     testCompileCommand(args[0], "<side>"),
			}
		}
		suggestions := []output.Suggestion{
			{Description: "To learn more about the test projects, see:", Command: usageDocsURL + "#rule-tests"},
			compile,
		}
		out.Suggestions(suggestions...)
	},
}

var testModelInitCmd = &cobra.Command{
	Use:   "init <test-project>",
	Short: "Create a dataflow model test project",
	Long:  "Create a dataflow model test project.\n\nArguments:\n  <test-project>  Directory of the new test project for dataflow models",
	Example: `  # Create a test project with samples that call Jackson
  opentaint test model init .opentaint/test-projects/my-model --language java \
    --dependency com.fasterxml.jackson.core:jackson-databind:2.17.2

  # Create a test project with Go samples that call Gin
  opentaint test model init .opentaint/test-projects/my-model --language go \
    --dependency github.com/gin-gonic/gin@v1.10.0`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		language := parseLanguage(initModelTestLanguage)
		dir := args[0]
		existing := checkTestProjectLanguage(dir, language)
		var err error
		if language == "go" {
			err = testproject.BootstrapGo(dir, goTestModulePath, initModelProjectDeps)
		} else {
			err = testproject.Bootstrap(dir, "model-test-project", initModelProjectDeps)
		}
		if err != nil {
			out.Fatal("Failed to create the test project", err)
		}
		if language == "go" {
			err = testmodel.ScaffoldGo(dir)
		} else {
			err = testmodel.Scaffold(dir)
		}
		if err != nil {
			out.Fatal("Failed to create the test samples", err)
		}
		printInitResult(existing, "the model test project", dir)
		out.Suggestions(
			output.Suggestion{Description: "To learn more about the test projects, see:", Command: usageDocsURL + "#model-tests"},
			output.Suggestion{Description: "To run the tests after you add the samples, first run:", Command: testCompileCommand(dir, "")},
		)
	},
}

// testCompileCommand returns the command that compiles a test project that init created in
// outputDir, or in its side directory when side is not empty. The side can be a placeholder.
// A test project in <root>/test-projects/<name> compiles to <root>/test-compiled/<name>, where
// the skills keep it. A test project elsewhere compiles to the default of compile.
func testCompileCommand(outputDir, side string) string {
	project := shellQuote(joinUserPath(outputDir))
	var compiled string
	clean := filepath.Clean(outputDir)
	if filepath.Base(filepath.Dir(clean)) == "test-projects" {
		compiled = shellQuote(joinUserPath(outputDir, "..", "..", "test-compiled", filepath.Base(clean)))
	}
	if side != "" {
		// The side is joined after quoting, so that a placeholder stays as it is.
		project += string(filepath.Separator) + side
		if compiled != "" {
			compiled += string(filepath.Separator) + side
		}
	}
	command := "opentaint compile " + project
	if compiled != "" {
		command += " -o " + compiled
	}
	return command
}

// checkTestProjectLanguage reports whether dir holds a test project in language. It stops the
// command when dir holds a test project in the other language: init would mix the two.
func checkTestProjectLanguage(dir, language string) bool {
	existing, err := existingTestProject(dir, language)
	if err != nil {
		out.Fatal("Failed to create the test project", err)
	}
	return existing
}

func existingTestProject(dir, language string) (bool, error) {
	switch other := testproject.Language(dir); other {
	case "":
		return false, nil
	case language:
		return true, nil
	default:
		return false, fmt.Errorf("`%s` is a %s test project", dir, languageName(other))
	}
}

// printInitResult prints what init did with the project at dir. For an existing project, it warns
// that init replaced the build file: the dependencies that it had and that --dependency does not
// repeat are gone. Init keeps the files of the user, such as the models, the samples, and rule-test.yaml.
func printInitResult(existing bool, project, dir string) {
	if existing {
		out.WarnDetails(fmt.Sprintf("Replaced the build file of `%s`", dir),
			"the new build file has only the libraries from --dependency")
		out.Successf("Updated %s at `%s`", project, dir)
		return
	}
	out.Successf("Created %s at `%s`", project, dir)
}

const (
	testDependencyUsage = "Library that the samples call: group:artifact:version or module@version (repeatable)"
	testLanguageUsage   = "Language of the samples: java or go (required)"
)

func init() {
	testRuleCmd.AddCommand(testRuleInitCmd)
	testRuleInitCmd.Flags().StringArrayVar(&initRuleProjectDeps, "dependency", nil, testDependencyUsage)
	testRuleInitCmd.Flags().StringVar(&initRuleLanguage, "language", "", testLanguageUsage)
	_ = testRuleInitCmd.MarkFlagRequired("language")
	testRuleInitCmd.Flags().BoolVar(&initRuleSinksOnly, "sinks-only", false,
		"Create only the sinks project")
	testRuleInitCmd.Flags().BoolVar(&initRuleSourcesOnly, "sources-only", false,
		"Create only the sources project")

	testModelCmd.AddCommand(testModelInitCmd)
	testModelInitCmd.Flags().StringArrayVar(&initModelProjectDeps, "dependency", nil, testDependencyUsage)
	testModelInitCmd.Flags().StringVar(&initModelTestLanguage, "language", "", testLanguageUsage)
	_ = testModelInitCmd.MarkFlagRequired("language")
	testApproximationCmd.AddCommand(deprecatedCommand(testModelInitCmd, "opentaint test approximation init", "opentaint test model init"))
}
