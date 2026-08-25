package cmd

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"

	"github.com/seqra/opentaint/internal/validation"
	"github.com/spf13/cobra"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/testmodel"
	"github.com/seqra/opentaint/internal/testproject"
	"github.com/seqra/opentaint/internal/testrule"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/seqra/opentaint/internal/utils/java"
	"github.com/seqra/opentaint/internal/utils/log"

	"github.com/seqra/opentaint/internal/output"
)

var OutputProjectModelPath string
var ProjectPath string
var DryRunCompile bool
var CompileLogFile string

// currentCompileBuilder returns a builder pre-populated with the user's current compile flags.
// All compile command suggestions should use this as the base to ensure that adding a new
// flag in one place automatically propagates to every suggestion.
func currentCompileBuilder(projectPath string) *utils.OpentaintCommandBuilder {
	return utils.NewCompileCommand(projectPath).
		WithOutput(OutputProjectModelPath)
}

// dockerCompileSuggestion builds the "try Docker-based compilation" fallback hint.
func dockerCompileSuggestion() output.Suggestion {
	return output.Suggestion{
		Description: "If the required Java is missing, set JAVA_HOME or compile in a container instead:",
		Command:     utils.BuildCompileCommandWithDocker(currentCompileBuilder(""), ProjectPath, OutputProjectModelPath),
	}
}

// compileCmd represents the compile command
var compileCmd = &cobra.Command{
	Use:   "compile <source-path>",
	Short: "Compile a Java, Kotlin, or Go project into a project model",
	Long:  "Compile a Java, Kotlin, or Go project into a project model.\n\nArguments:\n  <source-path>  Project root",
	Example: `  # Compile the project in the current directory
  opentaint compile .

  # Compile a rule test project
  opentaint compile .opentaint/test-projects/my-rule/sinks \
    -o .opentaint/test-compiled/my-rule/sinks`,
	Args:        cobra.ExactArgs(1), // require exactly one argument
	Annotations: map[string]string{"PrintConfig": "true"},
	Run: func(cmd *cobra.Command, args []string) {
		ProjectPath = args[0]

		projectRoot := filepath.Clean(ProjectPath)
		absProjectRoot := log.AbsPathOrExit(projectRoot, "project path")

		// The checks name the paths as the user wrote them. They resolve them against the
		// current directory, as the absolute paths are.
		if err := validation.ValidateSourceProjectForCompile(projectRoot); err != nil {
			out.FatalErr(err)
		}

		// Activate logging
		if !DryRunCompile {
			activateLoggingForProject(CompileLogFile, absProjectRoot)
		}

		if OutputProjectModelPath == "" {
			OutputProjectModelPath = utils.DefaultProjectModelPath(projectRoot)
		}
		outputProjectModelPath := filepath.Clean(OutputProjectModelPath)
		absOutputProjectModelPath := log.AbsPathOrExit(outputProjectModelPath, "output")

		sb := out.Section("OpenTaint Compile")
		addConfigFields(cmd, sb)
		if globals.Config.Output.Debug {
			sb.Line()
		}
		sb.FieldNode("Project", absProjectRoot).
			FieldNode("Project model", absOutputProjectModelPath).
			FieldGroup("Autobuilder", componentItems(resolveArtifactComponent("autobuilder"), false)...).
			Render()

		if err := validation.ValidateCompileInputs(projectRoot, outputProjectModelPath); err != nil {
			out.Blank()
			out.FatalErr(err)
		}
		if DryRunCompile {
			out.Blank()
			runDryRun("compilation", "compile the project")
			return
		}

		autobuilderJarPath, err := ensureAutobuilderAvailable()
		if err != nil {
			fail("Failed to get the autobuilder", err)
		}

		compileJavaRunner := newAutobuilderJavaRunner()
		if _, err := compileJavaRunner.EnsureJava(); err != nil {
			fail("Failed to find Java for the autobuilder", err)
		}

		if err := out.RunWithSpinner("Compiling project model", func() error {
			return compile(absProjectRoot, absOutputProjectModelPath, autobuilderJarPath, compileJavaRunner)
		}); err == nil {
			out.Blank()
			printCompileResult(outputProjectModelPath)
			suggest(compileNextStep(absProjectRoot, projectRoot, outputProjectModelPath))
		} else {
			failWith(1, "Failed to compile the project", err, dockerCompileSuggestion())
		}
	},
}

func init() {
	rootCmd.AddCommand(compileCmd)

	compileCmd.Flags().StringVarP(&OutputProjectModelPath, "output", "o", "", "Path to the new project model, which must not exist (default: .opentaint/project in the project)")
	compileCmd.Flags().BoolVar(&DryRunCompile, "dry-run", false, "Validate inputs and show what would run without compiling")
	compileCmd.Flags().StringVar(&CompileLogFile, "log-file", "", logFileUsage)
}

func compile(absProjectRoot, absOutputProjectModelPath, autobuilderJarPath string, javaRunner java.JavaRunner) error {
	if err := validation.ValidateCompileInputs(absProjectRoot, absOutputProjectModelPath); err != nil {
		return err
	}

	if err := utils.EnsureParentDir(absOutputProjectModelPath); err != nil {
		return err
	}

	if err := compileProject(absOutputProjectModelPath, absProjectRoot, autobuilderJarPath, javaRunner); err != nil {
		return err
	}

	if _, err := validation.ValidateProjectModelOutput(absOutputProjectModelPath); err != nil {
		output.LogInfo(fmt.Errorf("output validation failed after compile: %w", err))
		return invalidProjectModel(err)
	}

	return nil
}

// printCompileResult prints the line that ends a successful compile. projectModelPath is as the
// user wrote it.
func printCompileResult(projectModelPath string) {
	out.Successf("Created the project model at `%s`", projectModelPath)
}

func compileProject(absOutputProjectModelPath, absProjectRoot, autobuilderJarPath string, javaRunner java.JavaRunner) error {
	tempLogsDir, err := os.MkdirTemp("", "opentaint-*")
	if err != nil {
		return fmt.Errorf("failed to create temporary directory: %w", err)
	}
	return compileProjectWithLogs(absOutputProjectModelPath, absProjectRoot, autobuilderJarPath,
		filepath.Join(tempLogsDir, "autobuild.log"), false, javaRunner)
}

// noProjectModel explains an autobuilder run that wrote no project model. The runner reports such
// a run as failed whatever its exit code, so the exit code is a cause only when it is not 0.
func noProjectModel(cmdErr *java.JavaCommandError) error {
	const message = "the build produced no project model"
	if cmdErr.ExitCode == 0 {
		return errors.New(message)
	}
	return fmt.Errorf(message+": %w", cmdErr)
}

// invalidProjectModel explains an autobuilder run that wrote a project model that does not load.
func invalidProjectModel(err error) error {
	return fmt.Errorf("the build produced an invalid project model: %w", err)
}

// compileProjectWithLogs writes the autobuilder log to logsFile.
// captureBuildOutput adds the output from the build tool to this log.
func compileProjectWithLogs(absOutputProjectModelPath, absProjectRoot, autobuilderJarPath, tempLogsFile string, captureBuildOutput bool, javaRunner java.JavaRunner) error {
	var err error

	builder := NewAutobuilderBuilder().
		SetProjectRootDir(absProjectRoot).
		SetBuildMode("portable").
		SetResultDir(absOutputProjectModelPath).
		SetLogsFile(tempLogsFile).
		SetJarPath(autobuilderJarPath)

	if captureBuildOutput {
		builder.ForceDebugVerbosity()
	}

	autobuilderCommand := builder.BuildNativeCommand()

	commandSucceeded := func(_ error) bool {
		if _, err = os.Stat(absOutputProjectModelPath); err != nil {
			output.LogInfof("Output project model path does not exist after autobuilder execution: %s", absOutputProjectModelPath)
			output.LogInfo("Autobuilder failed to compile the project")
			return false
		}
		return true
	}
	// Execute the command using JavaRunner
	cmdErr, err := javaRunner.ExecuteJavaCommand(autobuilderCommand, commandSucceeded)
	if err != nil {
		output.LogInfof("Native compilation has failed: %s", err)
		return err
	}
	if cmdErr != nil {
		output.LogInfof("Native compilation has failed: %s", cmdErr)
		return noProjectModel(cmdErr)
	}

	return nil
}

// compileNextStep returns the hint printed after a successful compile. A compiled test project is
// tested, not scanned. projectRoot and projectModelPath are as the user wrote them.
func compileNextStep(absProjectRoot, projectRoot, projectModelPath string) (string, string) {
	if !utils.PathExists(filepath.Join(absProjectRoot, testproject.RuleTestFileName)) {
		return "To scan the compiled project model, run:", utils.BuildScanCommandFromCompile(projectRoot, projectModelPath)
	}
	projectModel := shellQuote(projectModelPath)
	if testmodel.IsTestProject(absProjectRoot) {
		return "To run the model tests, run:", "opentaint test model run " + projectModel + " --dataflow-models <model-project>"
	}
	command := "opentaint test rule run " + projectModel
	if utils.PathExists(filepath.Join(absProjectRoot, testrule.MarkersDir)) {
		command += " --ruleset " + shellQuote(joinUserPath(projectRoot, testrule.MarkersDir))
	}
	return "To run the rule tests, run:", command
}
