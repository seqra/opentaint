package cmd

import (
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"

	"github.com/seqra/opentaint/internal/testapprox"
	"github.com/seqra/opentaint/internal/testrule"
	"github.com/seqra/opentaint/internal/testutil"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/spf13/cobra"
)

var initRuleProjectDeps []string
var initApproxProjectDeps []string
var initRuleSinksOnly bool
var initRuleSourcesOnly bool

var testRuleInitCmd = &cobra.Command{
	Use:   "init <output-dir>",
	Short: "Bootstrap rule test projects (sinks and/or sources) with the generic Taint marker",
	Long: `Creates the rule test projects under <output-dir>: a 'sinks' project (a package's sink
lib rules tested against the generic Taint source) and a 'sources' project (a package's source
lib rules tested against the generic Taint sink). Pass --sinks-only or --sources-only for a
package that has only one side.

Each project includes:
  - build.gradle.kts with compile-only dependencies, settings.gradle.kts
  - libs/opentaint-sast-test-util.jar (provides @PositiveRuleSample and @NegativeRuleSample)
  - src/main/java/test/ with Taint.java (the generic source()/sink()) for test sample sources
  - test-rules/java/lib/test/generic-{source,sink}.yaml — the marker lib rules an agent refs
    from a test join; these and the test join live only here, never in .opentaint/rules, so
    they never reach the main project scan

Use --dependency to add Maven dependencies (e.g., servlet-api, Spring Web).`,
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
			bootstrapTestProject(dir, "opentaint-rule-test-"+kind, initRuleProjectDeps)
			if err := testrule.Scaffold(dir); err != nil {
				out.Fatalf("Failed to scaffold rule test project: %s", err)
			}
			fmt.Printf("Rule test project (%s) initialized at %s\n", kind, dir)
		}
	},
}

var testApproximationInitCmd = &cobra.Command{
	Use:   "init <output-dir>",
	Short: "Bootstrap a dataflow approximation test project with the fixed Taint source/sink and rule",
	Long: `Creates a minimal Gradle project structure for testing OpenTaint dataflow approximations.

The project includes:
  - build.gradle.kts with compile-only dependencies
  - settings.gradle.kts
  - libs/opentaint-sast-test-util.jar (provides @PositiveRuleSample and @NegativeRuleSample annotations)
  - approximation-rule.yaml, the fixed source->sink rule the samples are checked against
  - src/main/java/test/ with Taint.java (the fixed source() and sink()) for test sample sources

The approximation under test is NOT part of this project: it lives in its own unit folder
(.opentaint/approximations/<name>) and is applied at test time via --dataflow-approximations.

Use --dependency to add Maven dependencies (e.g., servlet-api, Spring Web).`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		bootstrapTestProject(args[0], "approximation-test-project", initApproxProjectDeps)
		if err := testapprox.Scaffold(args[0]); err != nil {
			out.Fatalf("Failed to scaffold approximation project: %s", err)
		}
		fmt.Printf("Approximation test project initialized at %s\n", args[0])
	},
}

func init() {
	testRuleCmd.AddCommand(testRuleInitCmd)
	testRuleInitCmd.Flags().StringArrayVar(&initRuleProjectDeps, "dependency", nil,
		"Maven dependency coordinates to add (e.g., 'javax.servlet:javax.servlet-api:4.0.1')")
	testRuleInitCmd.Flags().BoolVar(&initRuleSinksOnly, "sinks-only", false,
		"Scaffold only the sinks test project (a package with no sources)")
	testRuleInitCmd.Flags().BoolVar(&initRuleSourcesOnly, "sources-only", false,
		"Scaffold only the sources test project (a package with no sinks)")

	testApproximationCmd.AddCommand(testApproximationInitCmd)
	testApproximationInitCmd.Flags().StringArrayVar(&initApproxProjectDeps, "dependency", nil,
		"Maven dependency coordinates to add (e.g., 'javax.servlet:javax.servlet-api:4.0.1')")
}

// bootstrapTestProject creates the shared Gradle layout (dirs, test-util JAR, build files)
// used by both `test rule init` and `test approximation init`.
func bootstrapTestProject(outputDir, projectName string, dependencies []string) {
	dirs := []string{
		filepath.Join(outputDir, "libs"),
		filepath.Join(outputDir, "src", "main", "java", "test"),
	}
	for _, d := range dirs {
		if err := os.MkdirAll(d, 0o755); err != nil {
			out.Fatalf("Failed to create directory %s: %s", d, err)
		}
	}

	testUtilJarSrc, err := resolveTestUtilJar()
	if err != nil {
		out.Fatalf("Failed to resolve test-util JAR: %s", err)
	}
	testUtilJarDst := filepath.Join(outputDir, "libs", "opentaint-sast-test-util.jar")
	if err := copyFile(testUtilJarSrc, testUtilJarDst); err != nil {
		out.Fatalf("Failed to copy test-util JAR: %s", err)
	}

	if err := generateBuildGradle(outputDir, dependencies); err != nil {
		out.Fatalf("Failed to generate build.gradle.kts: %s", err)
	}

	if err := generateSettingsGradle(outputDir, projectName); err != nil {
		out.Fatalf("Failed to generate settings.gradle.kts: %s", err)
	}
}

// resolveTestUtilJar finds the opentaint-sast-test-util.jar.
// Resolution order:
//  1. Bundled path next to binary: <exe-dir>/lib/opentaint-sast-test-util.jar
//  2. Install path: ~/.opentaint/install/lib/opentaint-sast-test-util.jar
//  3. Dev build: <repo-root>/core/opentaint-sast-test-util/build/libs/opentaint-sast-test-util.jar
func resolveTestUtilJar() (string, error) {
	const jarName = "opentaint-sast-test-util.jar"

	// Tier 1: Bundled next to binary
	if libPath := utils.GetBundledLibPath(); libPath != "" {
		candidate := filepath.Join(libPath, jarName)
		if _, err := os.Stat(candidate); err == nil {
			return candidate, nil
		}
	}

	// Tier 2: Install path
	if libPath := utils.GetInstallLibPath(); libPath != "" {
		candidate := filepath.Join(libPath, jarName)
		if _, err := os.Stat(candidate); err == nil {
			return candidate, nil
		}
	}

	// Tier 3: Dev build — walk up from exe dir to find core/opentaint-sast-test-util/build/libs/
	if exe, err := os.Executable(); err == nil {
		exe, _ = filepath.EvalSymlinks(exe)
		// exe is typically at cli/bin/opentaint, so repo root is ../../
		dir := filepath.Dir(exe)
		for i := 0; i < 4; i++ {
			candidate := filepath.Join(dir, "core", "opentaint-sast-test-util", "build", "libs", jarName)
			if _, err := os.Stat(candidate); err == nil {
				return candidate, nil
			}
			dir = filepath.Dir(dir)
		}
	}

	// Tier 4: Extract from embedded binary
	if extracted, err := testutil.ExtractJar(); err == nil {
		return extracted, nil
	}

	return "", fmt.Errorf(
		"%s not found; build it with 'cd core && ./gradlew :opentaint-sast-test-util:jar' or reinstall opentaint",
		jarName,
	)
}

func copyFile(src, dst string) error {
	in, err := os.Open(src)
	if err != nil {
		return fmt.Errorf("open source: %w", err)
	}
	defer func() { _ = in.Close() }()

	if err := os.MkdirAll(filepath.Dir(dst), 0o755); err != nil {
		return fmt.Errorf("create parent dir: %w", err)
	}

	outFile, err := os.Create(dst)
	if err != nil {
		return fmt.Errorf("create destination: %w", err)
	}

	if _, err := io.Copy(outFile, in); err != nil {
		_ = outFile.Close()
		return fmt.Errorf("copy: %w", err)
	}

	if err := outFile.Close(); err != nil {
		return fmt.Errorf("close destination: %w", err)
	}
	return nil
}

func generateBuildGradle(outputDir string, dependencies []string) error {
	var sb strings.Builder
	sb.WriteString(`plugins {
    java
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

repositories {
    mavenCentral()
}

dependencies {
    compileOnly(files("libs/opentaint-sast-test-util.jar"))
`)
	for _, dep := range dependencies {
		sb.WriteString(fmt.Sprintf("    compileOnly(\"%s\")\n", dep))
	}
	sb.WriteString("}\n")

	path := filepath.Join(outputDir, "build.gradle.kts")
	return os.WriteFile(path, []byte(sb.String()), 0o644)
}

func generateSettingsGradle(outputDir, projectName string) error {
	content := fmt.Sprintf("rootProject.name = %q\n", projectName)
	path := filepath.Join(outputDir, "settings.gradle.kts")
	return os.WriteFile(path, []byte(content), 0o644)
}
