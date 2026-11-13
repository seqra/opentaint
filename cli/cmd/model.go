package cmd

import (
	"fmt"

	"github.com/seqra/opentaint/internal/models"
	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

var (
	initModelDeps     []string
	initModelLanguage string
)

var modelCmd = &cobra.Command{
	Use:   "model",
	Short: "Create dataflow model projects",
}

var modelInitCmd = &cobra.Command{
	Use:   "init <model-project>",
	Short: "Create a dataflow model project",
	Long:  "Create a dataflow model project.\n\nArguments:\n  <model-project>  Directory of the new model project",
	Example: `  # Create a model project for the Jackson version that the app uses
  opentaint model init .opentaint/dataflow --language java \
    --dependency com.fasterxml.jackson.core:jackson-databind:2.17.2

  # Create a model project for the Gin version that a Go app uses
  opentaint model init .opentaint/dataflow --language go \
    --dependency github.com/gin-gonic/gin@v1.10.0`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		language := parseLanguage(initModelLanguage)
		projectPath := log.AbsPathOrExit(args[0], "model-project")

		var existing bool
		if language == "go" {
			existing = initGoModel(projectPath, args[0])
		} else {
			existing = initJavaModel(projectPath, args[0])
		}

		printInitResult(existing, "the model project", args[0])
		out.Suggestions(
			output.Suggestion{Description: "To learn more about the dataflow models, see:", Command: usageDocsURL + "#opentaint-model"},
			output.Suggestion{Description: "To test the models after you write them, run:", Command: fmt.Sprintf("opentaint test model run <test-project-model> --dataflow-models %s", shellQuote(args[0]))},
		)
	},
}

// initJavaModel creates or updates a Java model project and reports whether it existed.
func initJavaModel(projectPath, projectArg string) bool {
	if models.IsGoProject(projectPath) {
		out.Fatal("Failed to create the model project", fmt.Errorf("`%s` is a Go model project", projectArg))
	}

	analyzerJarPath, err := ensureAnalyzerAvailable()
	if err != nil {
		out.Fatal("Failed to get the analyzer", err)
	}

	existing := models.IsProject(projectPath)
	if err := models.Scaffold(projectPath, initModelDeps, analyzerJarPath); err != nil {
		out.Fatal("Failed to create the model project", err)
	}
	return existing
}

// initGoModel creates or updates a Go model project and reports whether it existed.
func initGoModel(projectPath, projectArg string) bool {
	if models.IsProject(projectPath) {
		out.Fatal("Failed to create the model project", fmt.Errorf("`%s` is a Java model project", projectArg))
	}

	existing := models.IsGoProject(projectPath)
	if err := models.ScaffoldGo(projectPath, initModelDeps); err != nil {
		out.Fatal("Failed to create the model project", err)
	}
	return existing
}

func init() {
	rootCmd.AddCommand(modelCmd)
	modelCmd.AddCommand(modelInitCmd)

	modelInitCmd.Flags().StringArrayVar(&initModelDeps, "dependency", nil,
		"Library that the models refer to: group:artifact:version or module@version (repeatable)")
	modelInitCmd.Flags().StringVar(&initModelLanguage, "language", "", "Language of the models: java or go (required)")
	_ = modelInitCmd.MarkFlagRequired("language")

	approximationCmd := deprecatedGroup(modelCmd, "opentaint approximation", "opentaint model")
	approximationCmd.AddCommand(deprecatedCommand(modelInitCmd, "opentaint approximation init", "opentaint model init"))
	rootCmd.AddCommand(approximationCmd)
}
