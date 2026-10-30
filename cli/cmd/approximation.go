package cmd

import (
	"fmt"
	"strings"

	"github.com/seqra/opentaint/internal/approximation"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

var (
	initApproximationDeps     []string
	initApproximationLanguage string
)

var modelCmd = &cobra.Command{
	Use:   "model",
	Short: "Create dataflow model projects",
	Long: `A dataflow model project holds code-based models of how taint moves through
methods the analyzer cannot see into, together with the dependency versions those models
use.

Pass a project, or a directory that holds projects, to --dataflow-models.`,
}

var modelInitCmd = &cobra.Command{
	Use:   "init <output-dir>",
	Short: "Create a dataflow model project",
	Long: `Create an OpenTaint dataflow model project.

Use --language java to create a Java project. A Java project includes:
  - build.gradle.kts with compile-only dependencies, settings.gradle.kts
  - libs/opentaint-approximations-api.jar, the @Approximate annotations and the
    OpentaintNdUtil / ArgumentTypeContext support types
  - src/main/java/ for the model sources, one @Approximate class per target class

Use --language go to create a Go module with module path "opentaint". Put each model package
at the target import path below the module root. For example, model net/http in net/http.

Use --dependency to add each library the models use. For Java, use Maven coordinates. For
Go, use module@version. Use the versions from the target application.`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		projectPath := log.AbsPathOrExit(args[0], "output-dir")
		language := strings.ToLower(strings.TrimSpace(initApproximationLanguage))

		switch language {
		case "java":
			initJavaApproximation(projectPath, args[0])
		case "go":
			initGoApproximation(projectPath, args[0])
		default:
			out.Fatalf("Unsupported model language %q. Use java or go", initApproximationLanguage)
		}
	},
}

func initJavaApproximation(projectPath, projectArg string) {
	if approximation.IsGoProject(projectPath) {
		out.Fatalf("The output directory already contains a Go model project: %s", projectPath)
	}

	analyzerJarPath, err := ensureAnalyzerAvailable()
	if err != nil {
		out.Fatalf("Failed to resolve analyzer: %s", err)
	}

	// Init replaces the build file but keeps the model sources.
	// Warn the user because this removes dependency pins that they added manually.
	existing := approximation.IsProject(projectPath)
	if existing {
		out.Warnf("Replacing the build file of the existing model project at %s. "+
			"Pass every dependency the models need, not only the new ones", projectPath)
	}

	if err := approximation.Scaffold(projectPath, initApproximationDeps, analyzerJarPath); err != nil {
		out.Fatalf("Failed to create model project: %s", err)
	}

	printApproximationInitResult(projectPath, existing)
	suggest("To compile the models run", fmt.Sprintf("opentaint compile models %s", projectArg))
}

func initGoApproximation(projectPath, projectArg string) {
	if approximation.IsProject(projectPath) {
		out.Fatalf("The output directory already contains a Java model project: %s", projectPath)
	}

	existing := approximation.IsGoProject(projectPath)
	if existing {
		out.Warnf("Replacing go.mod in the existing model project at %s. "+
			"Pass every dependency the models need", projectPath)
	}

	if err := approximation.ScaffoldGo(projectPath, initApproximationDeps); err != nil {
		out.Fatalf("Failed to create Go model project: %s", err)
	}

	printApproximationInitResult(projectPath, existing)
	suggest("To apply the models run", fmt.Sprintf("opentaint scan <project> --dataflow-models %s", projectArg))
}

func printApproximationInitResult(projectPath string, existing bool) {
	if existing {
		fmt.Printf("Model project updated at %s\n", projectPath)
	} else {
		fmt.Printf("Model project initialized at %s\n", projectPath)
	}
}

func init() {
	rootCmd.AddCommand(modelCmd)
	modelCmd.AddCommand(modelInitCmd)

	modelInitCmd.Flags().StringArrayVar(&initApproximationDeps, "dependency", nil,
		"Maven coordinate for Java or module@version for Go (repeatable)")
	modelInitCmd.Flags().StringVar(&initApproximationLanguage, "language", "",
		"Model language: java or go")
	_ = modelInitCmd.MarkFlagRequired("language")

	approximationCmd := &cobra.Command{
		Use:        "approximation",
		Short:      modelCmd.Short,
		Deprecated: "use 'opentaint model' instead",
	}
	approximationCmd.AddCommand(deprecatedCommand(modelInitCmd, "init", "opentaint model init"))
	rootCmd.AddCommand(approximationCmd)
}
