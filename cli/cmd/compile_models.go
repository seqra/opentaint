package cmd

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"

	"github.com/seqra/opentaint/internal/autobuilder"
	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/models"
	"github.com/seqra/opentaint/internal/output"
)

// modelBuilder compiles a model project with the autobuilder.
// The model project supplies the compile dependencies.
type modelBuilder struct {
	analyzerJarPath string
	apiJar          []byte
	// failed reports that a compile failed after its spinner showed it.
	failed bool
}

func newModelBuilder(analyzerJarPath string) *modelBuilder {
	return &modelBuilder{analyzerJarPath: analyzerJarPath}
}

// Fingerprint identifies the compiler a build was produced with.
// The source stamp covers the model project but not the tool that reads it, so without
// this an upgraded CLI keeps serving models compiled by the previous one.
func (b *modelBuilder) Fingerprint() (string, error) {
	autobuilder := globals.ArtifactByKind("autobuilder")
	if autobuilder.Override == "" {
		return "autobuilder " + autobuilder.Version, nil
	}

	// A local autobuilder has no version to compare, so compare the file itself.
	info, err := os.Stat(autobuilder.Override)
	if err != nil {
		return "", fmt.Errorf("failed to read the autobuilder at %s: %w", autobuilder.Override, err)
	}
	return fmt.Sprintf("autobuilder %s %d %d",
		autobuilder.Override, info.Size(), info.ModTime().UnixNano()), nil
}

// Prepare updates the model API jar in the model project.
// The builder reads the jar from the analyzer only once.
func (b *modelBuilder) Prepare(projectDir string) error {
	if b.apiJar == nil {
		apiJar, err := models.ExtractApiJar(b.analyzerJarPath)
		if err != nil {
			return err
		}
		b.apiJar = apiJar
	}
	return models.WriteApiJar(projectDir, b.apiJar)
}

func (b *modelBuilder) Compile(projectDir, projectModelDir string) error {
	autobuilderJarPath, err := ensureAutobuilderAvailable()
	if err != nil {
		return fmt.Errorf("failed to resolve autobuilder: %w", err)
	}

	javaRunner := newAutobuilderJavaRunner()
	if _, err := javaRunner.EnsureJava(); err != nil {
		return fmt.Errorf("failed to resolve Java for model compilation: %w", err)
	}

	logsDir, err := os.MkdirTemp("", "opentaint-model-logs-*")
	if err != nil {
		return fmt.Errorf("failed to create temp directory for model build logs: %w", err)
	}
	logsFile := filepath.Join(logsDir, "model-build.log")

	// Show the spinner for direct and automatic builds.
	output.LogInfof("Compiling model project %s", projectDir)
	compile := func() error {
		return compileProjectWithLogs(projectModelDir, projectDir, autobuilderJarPath, logsFile, true, javaRunner)
	}
	if err := out.RunWithSpinner("Compiling model project "+filepath.Base(projectDir), compile); err != nil {
		b.failed = true
		output.LogInfof("Model project %s failed to build: %v", projectDir, err)
		// The compiler errors say all there is to say, so the log goes.
		if diagnostics := autobuilder.CompilerDiagnostics(logsFile); diagnostics != "" {
			_ = os.RemoveAll(logsDir)
			return fmt.Errorf("model project `%s` failed to compile:\n%s", projectDir, diagnostics)
		}
		return &modelBuildError{project: projectDir, log: logsFile, reason: autobuilder.BuildFailure(logsFile)}
	}

	_ = os.RemoveAll(logsDir)
	return nil
}

// modelBuildError reports a model project that failed to build for a reason other than a
// compiler error, such as a dependency that can not be resolved. Its build log holds the details.
type modelBuildError struct {
	project string
	log     string
	// reason is what the build tool reported, if it reported anything.
	reason string
}

func (e *modelBuildError) Error() string {
	if e.reason == "" {
		return fmt.Sprintf("model project `%s` failed to build", e.project)
	}
	return fmt.Sprintf("model project `%s` failed to build:\n%s", e.project, e.reason)
}

// modelBuildLogSuggestions points at the build log of a model project that failed to build.
func modelBuildLogSuggestions(err error) []output.Suggestion {
	var buildErr *modelBuildError
	if !errors.As(err, &buildErr) {
		return nil
	}
	return []output.Suggestion{{Description: "To see the full details, open the build log:", Command: buildErr.log}}
}
