package cmd

import (
	"fmt"
	"path/filepath"

	"github.com/seqra/opentaint/internal/testapprox"
	"github.com/seqra/opentaint/internal/testproject"
	"github.com/seqra/opentaint/internal/testrule"
	"github.com/seqra/opentaint/internal/testutil"
	"github.com/spf13/cobra"
)

var initRuleProjectDeps []string
var initApproxProjectDeps []string
var initRuleSinksOnly bool
var initRuleSourcesOnly bool

var testRuleInitCmd = &cobra.Command{
	Use:   "init <output-dir>",
	Short: "Create rule test projects with source and sink harnesses",
	Long: `Create one or two Gradle test projects under <output-dir>. The sinks
project tests sink rules against a generic Taint source; the sources project
tests source rules against a generic Taint sink. Use --sinks-only or
--sources-only when only one project is needed.

Each project includes:
  - build.gradle.kts with compile-only dependencies, settings.gradle.kts
  - libs/opentaint-sast-test-util.jar (provides @PositiveRuleSample and @NegativeRuleSample)
  - src/main/java/test/ with Taint.java (the generic source()/sink()) for test sample sources
  - test-rules/java/lib/test/generic-{source,sink}.yaml marker rules for test-only joins

Use --dependency to add compile-only Maven dependencies for the samples.`,
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
		jarSrc, err := testutil.ResolveJar()
		if err != nil {
			out.Fatalf("Failed to resolve test-util JAR: %s", err)
		}
		for _, kind := range kinds {
			dir := filepath.Join(args[0], kind)
			if err := testproject.Bootstrap(dir, "opentaint-rule-test-"+kind, initRuleProjectDeps, jarSrc); err != nil {
				out.Fatalf("Failed to bootstrap test project: %s", err)
			}
			if err := testrule.Scaffold(dir); err != nil {
				out.Fatalf("Failed to scaffold rule test project: %s", err)
			}
			fmt.Printf("Rule test project (%s) initialized at %s\n", kind, dir)
		}
	},
}

var testApproximationInitCmd = &cobra.Command{
	Use:   "init <output-dir>",
	Short: "Create a dataflow approximation test project",
	Long: `Create a minimal Gradle project for testing OpenTaint dataflow approximations.

The project includes:
  - build.gradle.kts with compile-only dependencies
  - settings.gradle.kts
  - libs/opentaint-sast-test-util.jar (provides @PositiveRuleSample and @NegativeRuleSample annotations)
  - approximation-rule.yaml, the fixed source-to-sink rule the samples are checked against
  - src/main/java/test/ with Taint.java (the fixed source() and sink()) for test sample sources

The approximation under test is supplied separately at test time with
--dataflow-approximations.

Use --dependency to add compile-only Maven dependencies for the samples.`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		jarSrc, err := testutil.ResolveJar()
		if err != nil {
			out.Fatalf("Failed to resolve test-util JAR: %s", err)
		}
		if err := testproject.Bootstrap(args[0], "approximation-test-project", initApproxProjectDeps, jarSrc); err != nil {
			out.Fatalf("Failed to bootstrap test project: %s", err)
		}
		if err := testapprox.Scaffold(args[0]); err != nil {
			out.Fatalf("Failed to scaffold approximation project: %s", err)
		}
		fmt.Printf("Approximation test project initialized at %s\n", args[0])
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
