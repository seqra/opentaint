package cmd

import (
	"errors"
	"os"
	"os/exec"
	"slices"

	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/utils/project"
	"github.com/seqra/opentaint/internal/validation"
)

const goInstallURL = "https://go.dev/dl/"

var installGoStep = output.Suggestion{Description: "To install Go, see:", Command: goInstallURL}

func goOnPath() bool {
	_, err := exec.LookPath("go")
	return err == nil
}

// requireGoToolchain stops the command when `go` is not on PATH.
func requireGoToolchain() {
	if goOnPath() {
		return
	}
	out.Blank()
	out.Error("Failed to find the Go toolchain", errors.New("the project has Go code, and `go` is not on PATH"))
	out.Suggestions(installGoStep)
	os.Exit(1)
}

// checkGoBeforeCompile checks for `go` before the build of sources with Go code: the autobuilder
// records the Go toolchain in the project model, and the analyzer skips a Go project without one.
// Sources with only Go code stop the command. With other code, the Go code is skipped, and the
// result is true.
func checkGoBeforeCompile(absUserProjectRoot string) bool {
	languages := validation.DetectLanguages(absUserProjectRoot)
	if !slices.Contains(languages, "Go") || goOnPath() {
		return false
	}
	if len(languages) == 1 {
		requireGoToolchain()
	}
	out.Blank()
	out.WarnDetails("Skipped the Go code", "`go` is not on PATH")
	out.Suggestions(installGoStep)
	return true
}

// checkGoToolchains reports the Go projects of a project model that the analyzer skips, as the
// model has no usable Go toolchain for them. It stops the command when the model has no other
// project. rebuildCommand rebuilds the project model; it is empty for a model that this run
// compiled.
func checkGoToolchains(config *project.Config, projectModelPath, rebuildCommand string) {
	skipped := config.SkippedGoProjects(projectModelPath)
	if len(skipped) == 0 {
		return
	}

	cause := skipped[0]
	var next []output.Suggestion
	hasGo := goOnPath()
	switch {
	case !hasGo && rebuildCommand == "":
		cause = "`go` is not on PATH"
		next = append(next, installGoStep)
	case !hasGo:
		next = append(next, installGoStep,
			output.Suggestion{Description: "After that, to rebuild the project model, run:", Command: rebuildCommand})
	case rebuildCommand != "":
		next = append(next,
			output.Suggestion{Description: "To rebuild the project model with the Go toolchain, run:", Command: rebuildCommand})
	default:
		// `go` is there, and the autobuilder of this run recorded none: the log has the reason.
		next = appendLogSuggestion(next)
	}

	out.Blank()
	if len(skipped) == len(config.GoProjects) && len(config.JavaProjects) == 0 {
		out.Error("Failed to analyze the Go code", errors.New(cause))
		out.Suggestions(next...)
		os.Exit(1)
	}
	out.WarnDetails("Skipped the Go code", cause)
	out.Suggestions(next...)
}

// warnNoGoToolchain warns after a compile that the project model has Go projects without a Go
// toolchain.
func warnNoGoToolchain(config *project.Config, projectModelPath string) {
	if len(config.SkippedGoProjects(projectModelPath)) == 0 {
		return
	}
	const message = "Recorded no Go toolchain in the project model"
	const effect = "a scan of this project model skips the Go code"
	out.Blank()
	if goOnPath() {
		out.WarnDetails(message, effect)
		out.Suggestions(appendLogSuggestion(nil)...)
		return
	}
	out.WarnDetails(message, "`go` is not on PATH", effect)
	out.Suggestions(installGoStep)
}

// goServerEnv returns the analyzer environment for the Go projects of a project model:
// GOIR_SERVER_BINARY with the path of the Go server. A model without a Go project to analyze
// needs none.
func goServerEnv(config *project.Config, projectModelPath string) map[string]string {
	if len(config.SkippedGoProjects(projectModelPath)) == len(config.GoProjects) {
		return nil
	}
	goServerPath, err := EnsureGoServerAvailable()
	if err != nil {
		failGoServer(err)
	}
	return map[string]string{"GOIR_SERVER_BINARY": goServerPath}
}
