package cmd

import (
	"fmt"
	"os"

	"github.com/seqra/opentaint/internal/models"
	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

var compileModelsOutput string

var compileModelsCmd = &cobra.Command{
	Use:   "models <model-project>",
	Short: "Compile a Java dataflow model project",
	Long:  "Compile a Java dataflow model project.\n\nArguments:\n  <model-project>  Model project from `opentaint model init`",
	Args:  cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		projectPath := log.AbsPathOrExit(args[0], "model-project")
		checkModelProject(args[0], projectPath)
		if models.IsGoProject(projectPath) {
			out.Printf("Nothing to compile: the analyzer reads the Go models in `%s` from source", args[0])
			suggestScanWithModels(args[0])
			return
		}

		outputPath := compileModelsOutput
		if outputPath == "" {
			outputPath = models.BuildDir(projectPath)
		} else {
			if err := models.CheckOutputDir(outputPath); err != nil {
				out.Fatal("Failed to compile the model project", err)
			}
			outputPath = log.AbsPathOrExit(outputPath, "output")
		}

		analyzerJarPath, err := ensureAnalyzerAvailable()
		if err != nil {
			out.Fatal("Failed to get the analyzer", err)
		}

		builder := newModelBuilder(analyzerJarPath, "Compiling model project")
		err = models.Build(projectPath, outputPath, builder)
		builder.step.Finish(err)
		if err != nil {
			out.Error("Failed to compile the model project", err)
			out.Suggestions(modelBuildLogSuggestions(err)...)
			os.Exit(1)
		}

		out.Blank()
		out.Section("Model Compile Summary").
			Field("Model project", projectPath).
			Field("Compiled models", outputPath).
			Render()
		suggestScanWithModels(args[0])
	},
}

// suggestScanWithModels suggests the scan that uses the models at projectArg.
func suggestScanWithModels(projectArg string) {
	suggest("To scan with these models, run:",
		fmt.Sprintf("opentaint scan <source-path> --dataflow-models %s", shellQuote(projectArg)))
}

func init() {
	compileCmd.AddCommand(compileModelsCmd)

	compileModelsCmd.Flags().StringVarP(&compileModelsOutput, "output", "o", "",
		"Path to the compiled models (default: <model-project>/.opentaint/build)")
	compileCmd.AddCommand(deprecatedCommand(compileModelsCmd, "opentaint compile approximations", "opentaint compile models"))
}

// checkModelProject stops the command when path is not a model project. It explains a wrong path
// as --dataflow-models does, and suggests init only for a directory that holds nothing yet.
func checkModelProject(path, absPath string) {
	const message = "Failed to compile the model project"
	if err := models.Check(path); err != nil {
		out.Error(message, err)
		out.Suggestions(modelProjectSuggestions(err)...)
		os.Exit(1)
	}
	if models.IsProject(absPath) || models.IsGoProject(absPath) {
		return
	}
	var suggestions []output.Suggestion
	if models.IsEmpty(absPath) {
		// Only Java models compile: the analyzer reads the Go models from source.
		suggestions = append(suggestions, javaModelInitStep(shellQuote(path)))
	}
	failWith(1, message, fmt.Errorf("`%s` is not a model project", path), suggestions...)
}
