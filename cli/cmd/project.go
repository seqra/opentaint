package cmd

import (
	"fmt"
	"os"
	"path/filepath"

	"github.com/spf13/cobra"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/seqra/opentaint/internal/utils/java"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/seqra/opentaint/internal/utils/project"
	"github.com/seqra/opentaint/internal/validation"
)

type JavaAutobuilderConfig struct {
	outputDir    string
	sourceRoot   string
	dependencies []string
	packages     []string
	classpaths   []string
}

type JavaAutobuilderBuilder struct {
	config *JavaAutobuilderConfig
}

func NewJavaAutobuilder() *JavaAutobuilderBuilder {
	return &JavaAutobuilderBuilder{
		config: &JavaAutobuilderConfig{},
	}
}

func (b *JavaAutobuilderBuilder) WithOutputDir(dir string) *JavaAutobuilderBuilder {
	cleanDir := filepath.Clean(dir)
	absDir := log.AbsPathOrExit(cleanDir, "output directory")
	b.config.outputDir = absDir
	return b
}

func (b *JavaAutobuilderBuilder) WithSourceRoot(root string) *JavaAutobuilderBuilder {
	cleanRoot := filepath.Clean(root)
	absRoot := log.AbsPathOrExit(cleanRoot, "source root")
	if _, err := os.Stat(absRoot); os.IsNotExist(err) {
		out.Fatalf("Source root `%s` does not exist", absRoot)
	}
	b.config.sourceRoot = absRoot
	return b
}

func (b *JavaAutobuilderBuilder) WithDependencies(deps []string) *JavaAutobuilderBuilder {
	absDeps := make([]string, len(deps))
	for i, dep := range deps {
		absDep, err := filepath.Abs(dep)
		if err != nil {
			out.Fatal(fmt.Sprintf("Failed to resolve the dependency path `%s`", dep), err)
		}
		if _, err := os.Stat(absDep); os.IsNotExist(err) {
			out.Fatalf("Dependency `%s` does not exist", absDep)
		}
		absDeps[i] = absDep
	}
	b.config.dependencies = absDeps
	return b
}

func (b *JavaAutobuilderBuilder) WithPackages(packages []string) *JavaAutobuilderBuilder {
	b.config.packages = packages
	return b
}

func (b *JavaAutobuilderBuilder) WithClasspath(classpath []string) *JavaAutobuilderBuilder {
	absClasspath := make([]string, len(classpath))
	for i, cp := range classpath {
		absCP, err := filepath.Abs(cp)
		if err != nil {
			out.Fatal(fmt.Sprintf("Failed to resolve the classpath entry `%s`", cp), err)
		}
		if _, err := os.Stat(absCP); os.IsNotExist(err) {
			out.Fatalf("Classpath entry `%s` does not exist", absCP)
		}
		absClasspath[i] = absCP
	}
	b.config.classpaths = absClasspath
	return b
}

func (b *JavaAutobuilderBuilder) Build() *JavaAutobuilderConfig {
	return b.config
}

func (c *JavaAutobuilderConfig) Execute() error {
	if err := c.validate(); err != nil {
		return err
	}

	return c.runAutobuilder()
}

func (c *JavaAutobuilderConfig) validate() error {
	if c.outputDir == "" {
		return fmt.Errorf("output directory is required")
	}
	if _, err := os.Stat(c.outputDir); err == nil {
		return fmt.Errorf("output directory `%s` already exists", c.outputDir)
	}
	if c.sourceRoot == "" {
		return fmt.Errorf("source root is required")
	}

	if len(c.classpaths) == 0 {
		return fmt.Errorf("at least one classpath is required")
	}
	if len(c.packages) == 0 {
		return fmt.Errorf("at least one package is required")
	}
	return nil
}

func (c *JavaAutobuilderConfig) runAutobuilder() error {
	autobuilderJarPath, err := ensureAutobuilderAvailable()
	if err != nil {
		return err
	}

	builder := NewAutobuilderBuilder().
		SetProjectRootDir(c.sourceRoot).
		SetResultDir(c.outputDir).
		SetBuildMode("portable").
		SetBuildType("cp").
		SetMaxMemory("-Xmx1G").
		SetJarPath(autobuilderJarPath)

	for _, cp := range c.classpaths {
		builder.AddClasspath(cp)
	}
	for _, dep := range c.dependencies {
		builder.AddDependency(dep)
	}
	for _, pkg := range c.packages {
		builder.AddPackage(pkg)
	}

	autobuilderCommand := builder.BuildNativeCommand()

	javaRunner := java.NewJavaRunner().
		WithSkipVerify(globals.Config.SkipVerify).
		WithDebugOutput(out.DebugStream("Autobuilder")).
		WithImageType(java.AdoptiumImageJRE).
		TrySpecificVersion(globals.DefaultJavaVersion)

	commandSucceeded := func(_ error) bool {
		if _, err = os.Stat(c.outputDir); err != nil {
			output.LogInfof("Output directory does not exist after autobuilder execution: %s", c.outputDir)
			output.LogInfo("Autobuilder failed to compile the project")
			return false
		}
		return true
	}

	cmdErr, err := javaRunner.ExecuteJavaCommand(autobuilderCommand, commandSucceeded)
	if err != nil {
		return fmt.Errorf("native autobuilder execution failed: %w", err)
	}
	if cmdErr != nil {
		return fmt.Errorf("native autobuilder execution failed: %w", cmdErr)
	}

	config, err := validation.ValidateProjectModelOutput(c.outputDir)
	if err != nil {
		return fmt.Errorf("output validation failed after project generation: %w", err)
	}

	return c.printProjectSummary(config)
}

func (c *JavaAutobuilderConfig) printProjectSummary(config *project.Config) error {
	projectYamlPath := filepath.Join(c.outputDir, "project.yaml")

	c.logProjectSummary(projectYamlPath, config)
	suggest("To scan the generated model, run:", utils.BuildScanCommandFromCompile(c.outputDir, c.outputDir))
	return nil
}

func (c *JavaAutobuilderConfig) logProjectSummary(projectYamlPath string, config *project.Config) {
	modules := config.AllModules()
	dependencies := config.AllDependencies()
	totalPackages := 0
	totalClasses := 0
	for _, module := range modules {
		totalPackages += len(module.Packages)
		totalClasses += len(module.ModuleClasses)
	}

	out.Blank()
	out.Section("Project Summary").
		Field("Generated project.yaml at", projectYamlPath).
		Line().
		Field("Total modules", len(modules)).
		Field("Total classes", totalClasses).
		Field("Total packages", totalPackages).
		Field("Total dependencies", len(dependencies)).
		Render()
}

var (
	OutputDir      string
	SourceRoot     string
	Dependencies   []string
	Packages       []string
	Classpaths     []string
	DryRunProject  bool
	ProjectLogFile string
)

var projectCmd = &cobra.Command{
	Use:   "project",
	Short: "Create a project model from precompiled JARs or classes",
	Long:  "Create a project model from precompiled JARs or classes. Use it when `opentaint compile` cannot build the project.",
	Example: `  # Create a project model from an application JAR and a library JAR
  opentaint project --source-root ./src --classpath ./app.jar \
    --package com.example --dependency ./lib/guava.jar -o .opentaint/project`,
	Run: func(cmd *cobra.Command, args []string) {
		config := NewJavaAutobuilder().
			WithOutputDir(OutputDir).
			WithSourceRoot(SourceRoot).
			WithDependencies(Dependencies).
			WithPackages(Packages).
			WithClasspath(Classpaths).
			Build()

		// Activate logging — derive cache slug from --output path
		if !DryRunProject {
			outputAbs := log.AbsPathOrExit(filepath.Clean(OutputDir), "output")
			activateLoggingForProject(ProjectLogFile, outputAbs)
		}

		classpathItems := make([]any, len(config.classpaths))
		for i, cp := range config.classpaths {
			classpathItems[i] = cp
		}
		packageItems := make([]any, len(config.packages))
		for i, pkg := range config.packages {
			packageItems[i] = pkg
		}

		sb := out.Section("OpenTaint Project").
			Field("Source root", config.sourceRoot).
			Field("Output", config.outputDir).
			Group("Classpaths", classpathItems...).
			Group("Packages", packageItems...)

		if len(config.dependencies) != 0 {
			depItems := make([]any, len(config.dependencies))
			for i, dep := range config.dependencies {
				depItems[i] = dep
			}
			sb.Group("Dependencies", depItems...)
		}
		sb.Render()

		if err := config.validate(); err != nil {
			out.Blank()
			out.FatalErr(err)
		}
		if DryRunProject {
			out.Blank()
			runDryRun("project-model generation", "create the project model")
			return
		}

		if err := config.Execute(); err != nil {
			fail("Failed to write the project model", err)
		}
	},
}

func init() {
	rootCmd.AddCommand(projectCmd)

	projectCmd.Flags().StringVarP(&OutputDir, "output", "o", "", "Path to the new project model, which must not exist (required)")
	_ = projectCmd.MarkFlagRequired("output")
	projectCmd.Flags().StringVar(&SourceRoot, "source-root", "", "Project source directory (required)")
	_ = projectCmd.MarkFlagRequired("source-root")
	projectCmd.Flags().StringArrayVar(&Dependencies, "dependency", []string{}, "Library JAR the project depends on (repeatable)")
	projectCmd.Flags().StringArrayVar(&Packages, "package", []string{}, "Package of the project's own code (repeatable, required)")
	_ = projectCmd.MarkFlagRequired("package")
	projectCmd.Flags().StringArrayVar(&Classpaths, "classpath", []string{}, "Class directory or JAR of the project (repeatable, required)")
	_ = projectCmd.MarkFlagRequired("classpath")
	projectCmd.Flags().BoolVar(&DryRunProject, "dry-run", false, "Validate inputs and show what would run without generating the project model")
	projectCmd.Flags().StringVar(&ProjectLogFile, "log-file", "", logFileUsage)
}
