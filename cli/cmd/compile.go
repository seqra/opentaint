package cmd

import (
	"fmt"
	"os"
	"path/filepath"

	"github.com/seqra/opentaint/internal/validation"
	"github.com/spf13/cobra"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/testmodel"
	"github.com/seqra/opentaint/internal/testproject"
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
	Short: "Compile a Java or Kotlin project into a project model",
	Long:  "Compile a Java or Kotlin project into a project model. Use it to scan one build more than once or to compile a test project.\n\nArguments:\n  <source-path>  Project root",
	Example: `  # Compile the project in the current directory
  opentaint compile . -o .opentaint/project

  # Compile a rule test project
  opentaint compile .opentaint/test-projects/my-rule/sinks \
    -o .opentaint/test-compiled/my-rule/sinks`,
	Args:        cobra.ExactArgs(1), // require exactly one argument
	Annotations: map[string]string{"PrintConfig": "true"},
	Run: func(cmd *cobra.Command, args []string) {
		ProjectPath = args[0]

		projectRoot := filepath.Clean(ProjectPath)
		absProjectRoot := log.AbsPathOrExit(projectRoot, "project path")

		if err := validation.ValidateSourceProjectForCompile(absProjectRoot); err != nil {
			out.FatalErr(err)
		}

		// Activate logging
		if !DryRunCompile {
			activateLoggingForProject(CompileLogFile, absProjectRoot)
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
			FieldNode("Autobuilder", utils.ArtifactVersionWithPath(globals.ArtifactByKind("autobuilder"))).
			Render()

		if DryRunCompile {
			out.Blank()
			failOnInvalidInputs(func() error { return validation.ValidateCompileInputs(absProjectRoot, absOutputProjectModelPath) })
			runDryRun("compilation")
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
			printCompileSummary(absOutputProjectModelPath)
			suggest(compileNextStep(absProjectRoot, projectRoot, absOutputProjectModelPath))
		} else {
			failWith(1, "Failed to compile the project", err, dockerCompileSuggestion())
		}
	},
}

func init() {
	rootCmd.AddCommand(compileCmd)

	compileCmd.Flags().StringVarP(&OutputProjectModelPath, "output", "o", "", "Path to the new project model, which must not exist (required)")
	_ = compileCmd.MarkFlagRequired("output")
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
		return fmt.Errorf("there was a problem during the compile step")
	}

	return nil
}

func printCompileSummary(absOutputProjectModelPath string) {
	out.Section("Compile Summary").
		Field("Project model written to", absOutputProjectModelPath).
		Render()
}

func compileProject(absOutputProjectModelPath, absProjectRoot, autobuilderJarPath string, javaRunner java.JavaRunner) error {
	tempLogsDir, err := os.MkdirTemp("", "opentaint-*")
	if err != nil {
		return fmt.Errorf("failed to create temporary directory: %w", err)
	}
	return compileProjectWithLogs(absOutputProjectModelPath, absProjectRoot, autobuilderJarPath,
		filepath.Join(tempLogsDir, "autobuild.log"), false, javaRunner)
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
		return fmt.Errorf("native compilation has failed: %w", err)
	}
	if cmdErr != nil {
		output.LogInfof("Native compilation has failed: %s", cmdErr)
		return fmt.Errorf("native compilation has failed: %w", cmdErr)
	}

	return nil
}

// compileNextStep returns the hint printed after a successful compile. A compiled test project is
// tested, not scanned.
func compileNextStep(absProjectRoot, projectRoot, absOutputProjectModelPath string) (string, string) {
	if !utils.PathExists(filepath.Join(absProjectRoot, testproject.RuleTestFileName)) {
		return "To scan the compiled project model, run:", utils.BuildScanCommandFromCompile(projectRoot, absOutputProjectModelPath)
	}
	projectModel := shellQuote(absOutputProjectModelPath)
	if testmodel.IsTestProject(absProjectRoot) {
		return "To run the model tests, run:", "opentaint test model run " + projectModel + " --dataflow-models <model>"
	}
	return "To run the rule tests, run:", "opentaint test rule run " + projectModel
}
