package cmd

import (
	"errors"
	"fmt"
	"os"
	"slices"

	"github.com/seqra/opentaint/internal/models"
	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

func addDataflowModelsFlag(cmd *cobra.Command, paths *[]string) {
	cmd.Flags().StringArrayVar(paths, "dataflow-models", nil,
		"Dataflow models: a model project, compiled models, or a directory of them (repeatable)")
	addDeprecatedFlagAlias(cmd.Flags(), "dataflow-models", "dataflow-approximations")
}

func addPassthroughModelsFlag(cmd *cobra.Command, paths *[]string) {
	cmd.Flags().StringArrayVar(paths, "passthrough-models", nil,
		"Pass-through models: a YAML file or a directory of them (repeatable)")
	addDeprecatedFlagAlias(cmd.Flags(), "passthrough-models", "passthrough-approximations")
}

// addDataflowModels resolves the paths to compiled model directories.
// It rebuilds a model project when its inputs change.
func addDataflowModels(b *AnalyzerBuilder, paths []string, analyzerJarPath string) {
	if len(paths) == 0 {
		return
	}

	absPaths := make([]string, 0, len(paths))
	for _, modelPath := range paths {
		absPaths = append(absPaths, log.AbsPathOrExit(modelPath, "dataflow-models"))
	}

	classDirs, err := models.ResolveAll(absPaths, newModelBuilder(analyzerJarPath))
	if err != nil {
		out.Error("Failed to load the dataflow models", err)
		out.Suggestions(append(modelProjectSuggestions(err, paths, absPaths), modelBuildLogSuggestions(err)...)...)
		os.Exit(1)
	}
	for _, classDir := range classDirs {
		b.AddDataflowApproximations(classDir)
	}
}

// modelProjectSuggestions returns the next steps for a model path that needs a model project.
// paths and absPaths are the model paths as the user wrote them and as absolute paths.
func modelProjectSuggestions(err error, paths, absPaths []string) []output.Suggestion {
	var needed *models.ProjectNeededError
	if !errors.As(err, &needed) {
		return nil
	}

	// The project goes in the model path itself, except for classes, which a project can not
	// take in: their models have to be written anew.
	projectArg := "<model-project>"
	if needed.Reason != models.PlainClasses {
		if i := slices.Index(absPaths, needed.Path); i >= 0 {
			projectArg = shellQuote(paths[i])
		}
	}
	return []output.Suggestion{{
		Description: "To create a model project, run:",
		Command:     fmt.Sprintf("opentaint model init %s --dependency <group:artifact:version>", projectArg),
	}}
}

func addPassthroughModels(b *AnalyzerBuilder, paths []string) {
	for _, passthrough := range paths {
		b.AddPassthroughApproximations(log.AbsPathOrExit(passthrough, "passthrough-models"))
	}
}
