package cmd

import (
	"fmt"
	"path/filepath"
	"strings"

	"github.com/seqra/opentaint/internal/approximation"
	"github.com/seqra/opentaint/internal/testapprox"
	"github.com/seqra/opentaint/internal/testproject"
	"github.com/seqra/opentaint/internal/testrule"
	"github.com/spf13/cobra"
)

var initRuleProjectDeps []string
var initApproxProjectDeps []string
var initRuleSinksOnly bool
var initRuleSourcesOnly bool
var initRuleLanguage string
var initApproxLanguage string

// testProjectModulePath is the module path of a Go test project, so samples are named test.<Function>.
const testProjectModulePath = "test"

var testRuleInitCmd = &cobra.Command{
	Use:   "init <output-dir>",
	Short: "Create rule test projects with source and sink harnesses",
	Long: `Create one or two test projects under <output-dir>. The sinks
project tests sink rules against a generic taint source; the sources project
tests source rules against a generic taint sink. Use --sinks-only or
--sources-only when only one project is needed.

Use --language java to create Gradle projects. Each project includes:
  - build.gradle.kts with compile-only dependencies, settings.gradle.kts
  - src/main/java/test/ with Taint.java (the generic source()/sink()) for test sample sources
  - test-rules/java/lib/test/generic-{source,sink}.yaml marker rules for test-only joins

Use --language go to create Go modules with module path "test". Each project includes:
  - go.mod with the required dependencies
  - taint/taint.go (the generic Source()/Sink()) for test sample sources
  - test-rules/go/lib/test/generic-{source,sink}.yaml marker rules for test-only joins

Positive and negative samples are specified via rule-test.yaml.

Use --dependency to add each library the samples use. For Java, use Maven coordinates. For
Go, use module@version. Use the versions from the target application.`,
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
		language := testProjectLanguage(initRuleLanguage)
		for _, kind := range kinds {
			dir := filepath.Join(args[0], kind)
			rejectOtherTestProjectLanguage(dir, language)
			switch language {
			case "java":
				if err := testproject.Bootstrap(dir, "opentaint-rule-test-"+kind, initRuleProjectDeps); err != nil {
					out.Fatalf("Failed to bootstrap test project: %s", err)
				}
				if err := testrule.Scaffold(dir); err != nil {
					out.Fatalf("Failed to scaffold rule test project: %s", err)
				}
			case "go":
				if err := testproject.BootstrapGo(dir, testProjectModulePath, initRuleProjectDeps); err != nil {
					out.Fatalf("Failed to bootstrap test project: %s", err)
				}
				if err := testrule.ScaffoldGo(dir); err != nil {
					out.Fatalf("Failed to scaffold rule test project: %s", err)
				}
			}
			fmt.Printf("Rule test project (%s) initialized at %s\n", kind, dir)
		}
		if language == "go" {
			suggest("After writing the samples, resolve their dependencies in each project with", "go mod tidy")
		}
	},
}

var testModelInitCmd = &cobra.Command{
	Use:   "init <output-dir>",
	Short: "Create a dataflow model test project",
	Long: `Create a minimal project for testing OpenTaint dataflow models.

Use --language java to create a Gradle project. The project includes:
  - build.gradle.kts with compile-only dependencies
  - settings.gradle.kts
  - approximation-rule.yaml, the fixed source-to-sink rule the samples are checked against
  - src/main/java/test/ with Taint.java (the fixed source() and sink()) for test sample sources

Use --language go to create a Go module with module path "test". The module includes:
  - go.mod with the required dependencies
  - approximation-rule.yaml, the fixed source-to-sink rule the samples are checked against
  - taint/taint.go (the fixed Source() and Sink()) for test sample sources

Positive and negative samples are specified via rule-test.yaml.

The models under test are supplied separately at test time with --dataflow-models.

Use --dependency to add each library the samples use. For Java, use Maven coordinates. For
Go, use module@version. Use the versions from the target application.`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		language := testProjectLanguage(initApproxLanguage)
		rejectOtherTestProjectLanguage(args[0], language)
		switch language {
		case "java":
			if err := testproject.Bootstrap(args[0], "model-test-project", initApproxProjectDeps); err != nil {
				out.Fatalf("Failed to bootstrap test project: %s", err)
			}
			if err := testapprox.Scaffold(args[0]); err != nil {
				out.Fatalf("Failed to scaffold model test project: %s", err)
			}
			fmt.Printf("Model test project initialized at %s\n", args[0])
		case "go":
			if err := testproject.BootstrapGo(args[0], testProjectModulePath, initApproxProjectDeps); err != nil {
				out.Fatalf("Failed to bootstrap test project: %s", err)
			}
			if err := testapprox.ScaffoldGo(args[0]); err != nil {
				out.Fatalf("Failed to scaffold model test project: %s", err)
			}
			fmt.Printf("Model test project initialized at %s\n", args[0])
			suggest("After writing the samples, resolve their dependencies with", "go mod tidy")
		}
	},
}

// testProjectLanguage normalizes a --language value to java or go.
func testProjectLanguage(value string) string {
	language := strings.ToLower(strings.TrimSpace(value))
	if language != "java" && language != "go" {
		out.Fatalf("Unsupported test project language %q. Use java or go", value)
	}
	return language
}

// rejectOtherTestProjectLanguage stops when dir already holds a test project in the other language.
func rejectOtherTestProjectLanguage(dir, language string) {
	if err := otherTestProjectLanguage(dir, language); err != nil {
		out.Fatalf("%s", err)
	}
}

func otherTestProjectLanguage(dir, language string) error {
	switch {
	case language == "java" && approximation.IsGoProject(dir):
		return fmt.Errorf("the output directory already contains a Go test project: %s", dir)
	case language == "go" && approximation.IsProject(dir):
		return fmt.Errorf("the output directory already contains a Java test project: %s", dir)
	}
	return nil
}

func init() {
	testRuleCmd.AddCommand(testRuleInitCmd)
	testRuleInitCmd.Flags().StringArrayVar(&initRuleProjectDeps, "dependency", nil,
		"Maven coordinate for Java or module@version for Go (repeatable)")
	testRuleInitCmd.Flags().StringVar(&initRuleLanguage, "language", "",
		"Test project language: java or go")
	_ = testRuleInitCmd.MarkFlagRequired("language")
	testRuleInitCmd.Flags().BoolVar(&initRuleSinksOnly, "sinks-only", false,
		"Create only the sinks test project")
	testRuleInitCmd.Flags().BoolVar(&initRuleSourcesOnly, "sources-only", false,
		"Create only the sources test project")

	testModelCmd.AddCommand(testModelInitCmd)
	testModelInitCmd.Flags().StringArrayVar(&initApproxProjectDeps, "dependency", nil,
		"Maven coordinate for Java or module@version for Go (repeatable)")
	testModelInitCmd.Flags().StringVar(&initApproxLanguage, "language", "",
		"Test project language: java or go")
	_ = testModelInitCmd.MarkFlagRequired("language")
	testApproximationCmd.AddCommand(deprecatedCommand(testModelInitCmd, "init", "opentaint test model init"))
}
