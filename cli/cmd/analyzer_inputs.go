package cmd

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"

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

// checkModelInputs stops the command when a model path holds no models. It builds nothing, so
// it runs with the other input checks, before the long steps.
func checkModelInputs(dataflow, passthrough []string) {
	for _, path := range dataflow {
		if err := models.Check(path); err != nil {
			out.Blank()
			out.Error("Failed to load the dataflow models", err)
			out.Suggestions(modelProjectSuggestions(err)...)
			os.Exit(1)
		}
	}
	for _, path := range passthrough {
		if err := checkPassthroughPath(path); err != nil {
			out.Blank()
			out.Fatal("Failed to load the pass-through models", err)
		}
	}
}

// checkPassthroughPath rejects a pass-through path that the analyzer would read nothing from
// although it holds something: the analyzer reads only the YAML files in the tree of the path.
// A directory with no files holds no models and is accepted, as for the dataflow models.
func checkPassthroughPath(path string) error {
	info, err := os.Stat(path)
	if os.IsNotExist(err) {
		return fmt.Errorf("`%s` does not exist", path)
	}
	if err != nil {
		return fmt.Errorf("failed to access `%s`: %w", path, err)
	}
	if !info.IsDir() {
		if !isYAMLFile(path) {
			return fmt.Errorf("`%s` is not a pass-through model", path)
		}
		return nil
	}

	var yamlFiles, otherFiles bool
	err = filepath.WalkDir(path, func(file string, entry os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if file == path {
			return nil
		}
		if strings.HasPrefix(entry.Name(), ".") {
			if entry.IsDir() {
				return filepath.SkipDir
			}
			return nil
		}
		if entry.IsDir() {
			return nil
		}
		if isYAMLFile(file) {
			yamlFiles = true
			return filepath.SkipAll
		}
		otherFiles = true
		return nil
	})
	if err != nil {
		return fmt.Errorf("failed to read `%s`: %w", path, err)
	}
	if otherFiles && !yamlFiles {
		return fmt.Errorf("`%s` contains no pass-through models", path)
	}
	return nil
}

func isYAMLFile(path string) bool {
	ext := strings.ToLower(filepath.Ext(path))
	return ext == ".yaml" || ext == ".yml"
}

// compileDataflowModels returns the class directories of the dataflow models. It compiles a
// model project when its inputs change.
func compileDataflowModels(paths []string, analyzerJarPath string) []string {
	if len(paths) == 0 {
		return nil
	}

	absPaths := make([]string, 0, len(paths))
	for _, modelPath := range paths {
		absPaths = append(absPaths, log.AbsPathOrExit(modelPath, "dataflow-models"))
	}

	builder := newModelBuilder(analyzerJarPath, "Compiling model projects")
	classDirs, err := models.ResolveAll(absPaths, builder)
	builder.step.Finish(err)
	if err != nil {
		out.Error("Failed to load the dataflow models", err)
		out.Suggestions(modelBuildLogSuggestions(err)...)
		os.Exit(1)
	}
	return classDirs
}

// modelProjectSuggestions returns the next steps for a model path that needs a model project.
func modelProjectSuggestions(err error) []output.Suggestion {
	var needed *models.ProjectNeededError
	if !errors.As(err, &needed) {
		return nil
	}

	// The project goes in the model path itself, except for classes, which a project can not
	// take in: their models have to be written anew.
	projectArg := "<model-project>"
	if needed.Reason != models.PlainClasses {
		projectArg = shellQuote(needed.Path)
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
