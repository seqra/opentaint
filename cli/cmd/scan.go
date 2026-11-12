package cmd

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/seqra/opentaint/internal/analyzer"
	"github.com/seqra/opentaint/internal/load_trace"
	"github.com/seqra/opentaint/internal/rules"
	"github.com/seqra/opentaint/internal/sarif"
	"github.com/seqra/opentaint/internal/validation"
	"github.com/seqra/opentaint/internal/version"

	"github.com/seqra/opentaint/internal/utils/project"
	"github.com/spf13/cobra"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/seqra/opentaint/internal/utils/java"
	"github.com/seqra/opentaint/internal/utils/log"
)

type ScanConfig struct {
	UserProjectPath           string
	ProjectModelPath          string
	SarifReportPath           string
	SemgrepCompatibilitySarif bool
	Severity                  []string
	Ruleset                   []string
	DryRun                    bool
	Recompile                 bool
	LogFile                   string
	RuleID                    []string
	PassthroughModels         []string
	DataflowModels            []string
	TrackExternalMethods      bool
	IterationLimit            int

	DebugFactReachabilitySarif            bool
	DebugRunAnalysisOnSelectedEntryPoints string
	ExpandRuleRefs                        bool
}

var scanFlags ScanConfig

type RulesetType struct {
	Path    string
	Builtin bool
}

const (
	dryRunScanProjectModelPath  = "opentaint-scan-dry-run/project-model"
	dryRunRuleLoadTraceFileName = "opentaint-rule-load-trace.dry-run.json"
)

type scanPlan struct {
	absProjectModel  string // absolute path to the project model (always the cache dir when projectCachePath is set)
	projectCachePath string // cache dir for this project (empty for explicit model / dry-run)
	needsCompilation bool   // true when compilation is needed before scanning
	cacheLock        *utils.FileLock
}

func (p scanPlan) title() string {
	if p.needsCompilation {
		return "OpenTaint Compile and Scan"
	}
	return "OpenTaint Scan"
}

// scanCmd represents the scan command
var scanCmd = &cobra.Command{
	Use:   "scan [<source-path>]",
	Short: "Scan a Java or Kotlin project for vulnerabilities",
	Long:  "Build a Java or Kotlin project and scan it for vulnerabilities.\n\nArguments:\n  [<source-path>]  Project root (default: the current directory)",
	Example: `  # Scan the project in the current directory
  opentaint scan . -o .opentaint/results/report.sarif

  # Scan a large project with more memory and time
  opentaint scan . --max-memory 16G --timeout 20m

  # Add your own rules and dataflow models to the built-in ones
  opentaint scan . --ruleset builtin --ruleset .opentaint/rules \
    --dataflow-models .opentaint/dataflow`,
	Args:        cobra.MaximumNArgs(1),
	Annotations: map[string]string{"PrintConfig": "true"},
	Run: func(cmd *cobra.Command, args []string) {
		if scanFlags.DebugRunAnalysisOnSelectedEntryPoints != "" {
			out.Warn("On Spring projects, this method is added to the auto-discovered entry points, not used to restrict them")
		}
		runScan(cmd, prepareScanConfig(scanFlags, args))
	},
}

func prepareScanConfig(cfg ScanConfig, args []string) ScanConfig {
	if len(args) > 0 && cfg.ProjectModelPath != "" {
		out.Errorf("Cannot use both <source-path> and --project-model")
		suggest("Use either a source path or --project-model:",
			utils.NewScanCommand("<source-path>").Build()+"\n  "+utils.NewScanCommand("").WithProjectModel("<project-model>").Build())
		os.Exit(1)
	}
	if cfg.Recompile && cfg.ProjectModelPath != "" {
		out.Fatalf("Cannot use --recompile with --project-model")
	}
	if len(args) > 0 {
		cfg.UserProjectPath = args[0]
	} else {
		cfg.UserProjectPath = "."
	}
	return cfg
}

func init() {
	rootCmd.AddCommand(scanCmd)
	addScanFlags(scanCmd)
	addRuleIDFlag(scanCmd)
	addEntryPointsFlag(scanCmd)
}

// entryPointsUsage describes the --entry-points flag of scan and test rule reachability.
const entryPointsUsage = "Start analysis from a fully qualified method such as com.example.Class#method, or '*' for every method"

func addEntryPointsFlag(cmd *cobra.Command) {
	cmd.Flags().StringVar(&scanFlags.DebugRunAnalysisOnSelectedEntryPoints, "entry-points", "", entryPointsUsage)
	_ = cmd.Flags().MarkHidden("entry-points")
}

func addRuleIDFlag(cmd *cobra.Command) {
	cmd.Flags().StringArrayVar(&scanFlags.RuleID, "rule-id", nil, "Run only the rule with this ID (repeatable)")
}

func addScanFlags(cmd *cobra.Command) {
	cmd.Flags().DurationVarP(&globals.Config.Scan.Timeout, "timeout", "t", 900*time.Second, "Analysis timeout (e.g. 30m, 1h)")

	cmd.Flags().StringArrayVar(&scanFlags.Ruleset, "ruleset", []string{"builtin"}, "Rules file or directory, or builtin for the built-in ruleset (repeatable)")

	cmd.Flags().BoolVar(&scanFlags.SemgrepCompatibilitySarif, "semgrep-compatibility-sarif", true, "Use Semgrep-style dotted rule IDs in the SARIF report")
	cmd.Flags().StringVarP(&scanFlags.SarifReportPath, "output", "o", "", "Path to the SARIF report (default: .opentaint/results/report.sarif in the project)")

	cmd.Flags().StringArrayVar(&scanFlags.Severity, "severity", []string{"warning", "error"}, "Run only the rules of this severity: note, warning, or error (repeatable)")
	cmd.Flags().StringVar(&globals.Config.Scan.MaxMemory, "max-memory", "8G", "Maximum analyzer heap size (e.g. 8G, 1024m)")
	cmd.Flags().Int64Var(&globals.Config.Scan.CodeFlowLimit, "code-flow-limit", 0, "Maximum number of code flows per finding (0 = unlimited)")
	cmd.Flags().BoolVar(&scanFlags.DryRun, "dry-run", false, "Validate inputs and show what would run without compiling or scanning")
	cmd.Flags().BoolVar(&scanFlags.Recompile, "recompile", false, "Rebuild the project even if a cached project model exists")
	cmd.Flags().StringVar(&scanFlags.ProjectModelPath, "project-model", "", "Path to a compiled project model to scan")
	cmd.Flags().StringVar(&scanFlags.LogFile, "log-file", "", logFileUsage)

	addPassthroughModelsFlag(cmd, &scanFlags.PassthroughModels)

	addDataflowModelsFlag(cmd, &scanFlags.DataflowModels)

	cmd.Flags().BoolVar(&scanFlags.TrackExternalMethods, "track-external-methods", false, "Write external-method coverage files next to the SARIF report")

	cmd.Flags().IntVar(&scanFlags.IterationLimit, "iteration-limit", 0, "Cap the iterative-deepening fact depth at N field accessors (0 = unlimited)")
}

// currentScanBuilder returns a builder pre-populated with the user's current scan flags.
func currentScanBuilder(cfg ScanConfig, sourcePath string) *utils.OpentaintCommandBuilder {
	b := utils.NewScanCommand(sourcePath).
		WithOutput(cfg.SarifReportPath).
		WithTimeout(globals.Config.Scan.Timeout).
		WithRuleset(cfg.Ruleset).
		WithSemgrepCompatibility(cfg.SemgrepCompatibilitySarif).
		WithRuleID(cfg.RuleID).
		WithPassthroughModels(cfg.PassthroughModels).
		WithDataflowModels(cfg.DataflowModels).
		WithTrackExternalMethods(cfg.TrackExternalMethods).
		WithIterationLimit(cfg.IterationLimit)
	if !isDefaultSeverity(cfg.Severity) {
		b.WithSeverity(cfg.Severity)
	}
	return b
}

func isDefaultSeverity(sev []string) bool {
	return len(sev) == 2 && sev[0] == "warning" && sev[1] == "error"
}

// dockerScanSuggestion builds the "try Docker-based scan" fallback hint.
func dockerScanSuggestion(cfg ScanConfig, projectRoot, sarifReportPath string) output.Suggestion {
	return output.Suggestion{
		Description: "If the required Java is missing, set JAVA_HOME or scan in a container instead:",
		Command:     utils.BuildScanCommandWithDocker(currentScanBuilder(cfg, ""), projectRoot, sarifReportPath, cfg.Ruleset),
	}
}

func runScan(cmd *cobra.Command, cfg ScanConfig) {
	userProjectPath := filepath.Clean(cfg.UserProjectPath)
	absUserProjectRoot := log.AbsPathOrExit(userProjectPath, "project path")

	if !utils.IsSupportedArch() {
		out.Fatalf("Unsupported architecture `%s`, OpenTaint runs on amd64 and arm64", utils.GetArch())
	}

	// When compiling from sources, validate the source folder looks like a Java/Kotlin project
	if cfg.ProjectModelPath == "" {
		if err := validation.ValidateSourceProject(absUserProjectRoot); err != nil {
			if validation.IsProjectModel(absUserProjectRoot) {
				out.ErrorErr(err)
				suggest("To scan the project model, run:", currentScanBuilder(cfg, "").WithProjectModel(absUserProjectRoot).Build())
				os.Exit(1)
			}
			out.FatalErr(err)
		}
	}

	plan := resolveScanPlan(cfg, absUserProjectRoot)
	defer func() {
		if plan.cacheLock != nil {
			plan.cacheLock.Unlock()
		}
	}()

	// Activate logging
	if !cfg.DryRun {
		activateLoggingForProject(cfg.LogFile, absUserProjectRoot)
	}

	absProjectModelPath := plan.absProjectModel

	var absRuleSetPaths []RulesetType
	var userRuleSetPath = cfg.Ruleset

	for _, ruleset := range userRuleSetPath {
		switch ruleset {
		case "builtin":
			rulesPath, err := utils.GetRulesPath(globals.Config.Rules.Version)
			if err != nil {
				out.Fatal("Failed to find the built-in ruleset", err)
			}

			absRuleSetPaths = append(absRuleSetPaths, RulesetType{Path: rulesPath, Builtin: true})
		default:
			rulesPath := log.AbsPathOrExit(ruleset, "ruleset")
			absRuleSetPaths = append(absRuleSetPaths, RulesetType{Path: rulesPath, Builtin: false})
		}

	}

	var absSarifReportPath string
	if cfg.SarifReportPath != "" {
		absSarifReportPath = log.AbsPathOrExit(cfg.SarifReportPath, "output")
	} else if cfg.ProjectModelPath == "" {
		absSarifReportPath = utils.DefaultSarifReportPath(absUserProjectRoot)
	} else {
		absSarifReportPath = utils.ProjectModelSarifReportPath(absProjectModelPath)
	}

	sarifReportName := filepath.Base(absSarifReportPath)

	localVersion := utils.ArtifactDisplayVersion(globals.ArtifactByKind("analyzer"))
	localSemanticVersion := version.GetVersion()

	var sourceRoot string
	if !plan.needsCompilation {
		if parsedSourceRoot, err := project.GetSourceRoot(absProjectModelPath); err != nil {
			out.Fatal("Failed to read the source root of the project model", err)
		} else {
			sourceRoot = parsedSourceRoot
		}
	} else {
		sourceRoot = absUserProjectRoot
	}

	uriBase := fmt.Sprintf("%s%s", sourceRoot, string(filepath.Separator))

	ruleLoadTraceDir, err := utils.GetProjectLogPath(absUserProjectRoot)
	if err != nil {
		out.Fatal("Failed to prepare the rule load trace", err)
	}

	var absSemgrepRuleLoadTracePath string
	if cfg.DryRun {
		absSemgrepRuleLoadTracePath = filepath.Join(ruleLoadTraceDir, dryRunRuleLoadTraceFileName)
	} else {
		absSemgrepRuleLoadTracePath = setupSemgrepRuleLoadTrace(ruleLoadTraceDir)
	}

	// Display scan information in tree format
	printScanInfo(cmd, plan, absSemgrepRuleLoadTracePath, absUserProjectRoot, absRuleSetPaths)

	var nonBuiltinRulesetPaths []string
	for _, r := range absRuleSetPaths {
		if !r.Builtin {
			nonBuiltinRulesetPaths = append(nonBuiltinRulesetPaths, r.Path)
		}
	}

	maxMemory, err := validation.ValidateScanInputs(absUserProjectRoot, absProjectModelPath, absSarifReportPath, nonBuiltinRulesetPaths, cfg.Severity, globals.Config.Scan.MaxMemory, !plan.needsCompilation)
	if err != nil {
		out.Blank()
		out.FatalErr(err)
	}
	checkModelInputs(cfg.DataflowModels, cfg.PassthroughModels)

	if cfg.DryRun {
		out.Blank()
		runDryRun("the build and scan", "scan the project")
		return
	}

	hasBuiltin := false
	for _, ruleSetPath := range absRuleSetPaths {
		if ruleSetPath.Builtin {
			hasBuiltin = true
			break
		}
	}
	if hasBuiltin {
		if _, err := utils.EnsureRulesPath(out); err != nil {
			fail("Failed to prepare the built-in ruleset", err)
		}
	}

	analyzerJarPath, err := ensureAnalyzerAvailable()
	if err != nil {
		fail("Failed to get the analyzer", err)
	}
	// The models compile in less time than the project, so an error in them comes first.
	dataflowClassDirs := compileDataflowModels(cfg.DataflowModels, analyzerJarPath)

	if plan.needsCompilation {
		autobuilderJarPath, err := ensureAutobuilderAvailable()
		if err != nil {
			fail("Failed to get the autobuilder", err)
		}

		compileJavaRunner := newAutobuilderJavaRunner()
		if _, err := compileJavaRunner.EnsureJava(); err != nil {
			fail("Failed to find Java for the autobuilder", err)
		}

		// Wipe any residue from a prior crashed compile before writing new output.
		if plan.projectCachePath != "" {
			if err := os.RemoveAll(plan.absProjectModel); err != nil {
				fail("Failed to prepare the project model cache", err)
			}
		}

		if err := out.RunWithSpinner("Compiling project model", func() error {
			return compile(absUserProjectRoot, plan.absProjectModel, autobuilderJarPath, compileJavaRunner)
		}); err != nil {
			if plan.projectCachePath != "" {
				_ = os.RemoveAll(plan.absProjectModel)
			}
			failWith(1, "Failed to compile the project", err, dockerScanSuggestion(cfg, absUserProjectRoot, absSarifReportPath))
		}
		out.Blank()

		// Mark the cache as valid, then downgrade to a reader so other scans
		// can run the analyzer against the freshly-compiled model in parallel.
		if plan.projectCachePath != "" {
			if err := utils.MarkCompileComplete(plan.projectCachePath); err != nil {
				_ = os.RemoveAll(plan.absProjectModel)
				fail("Failed to mark the project model as complete", err)
			}
			if err := plan.cacheLock.Downgrade(); err != nil {
				output.LogInfof("Cache lock downgrade failed, continuing under exclusive: %v", err)
			}
		}

		printCompileSummary(absProjectModelPath)
	}

	if err := utils.EnsureParentDir(absSarifReportPath); err != nil {
		fail("Failed to create the output directory", err)
	}

	// Update builder with native paths for native execution
	nativeProjectPath := filepath.Join(absProjectModelPath, "project.yaml")
	nativeOutputDir := filepath.Dir(absSarifReportPath)
	nativeBuilder := NewAnalyzerBuilder().
		SetProject(nativeProjectPath).
		SetOutputDir(nativeOutputDir).
		SetSarifFileName(sarifReportName).
		SetSarifCodeFlowLimit(globals.Config.Scan.CodeFlowLimit).
		SetSarifToolVersion(localVersion).
		SetSarifToolSemanticVersion(localSemanticVersion).
		SetSarifUriBase(uriBase).
		SetIfdsAnalysisTimeout(int64(globals.Config.Scan.Timeout / time.Second)).
		SetRuleLoadTracePath(absSemgrepRuleLoadTracePath).
		EnablePartialFingerprints()
	if cfg.SemgrepCompatibilitySarif {
		nativeBuilder.EnableSemgrepCompatibility()
	}
	for _, severity := range cfg.Severity {
		nativeBuilder.AddSeverity(severity)
	}
	for _, absRuleSetPath := range absRuleSetPaths {
		nativeBuilder.AddRuleSet(absRuleSetPath.Path)
	}
	if maxMemory != "" {
		nativeBuilder.SetMaxMemory(maxMemory)
	}
	ruleIDs := cfg.RuleID
	if cfg.ExpandRuleRefs && len(ruleIDs) > 0 {
		var roots []string
		for _, r := range absRuleSetPaths {
			roots = append(roots, r.Path)
		}
		ruleIDs = rules.ExpandRuleIDs(ruleIDs, roots)
	}
	for _, ruleID := range ruleIDs {
		nativeBuilder.AddRuleID(ruleID)
	}
	addPassthroughModels(nativeBuilder, cfg.PassthroughModels)
	if cfg.TrackExternalMethods {
		nativeBuilder.SetTrackExternalMethods(true)
	}
	if cfg.IterationLimit > 0 {
		nativeBuilder.SetIterationLimit(int64(cfg.IterationLimit))
	}
	if cfg.DebugFactReachabilitySarif {
		nativeBuilder.EnableDebugFactReachabilitySarif()
	}
	if cfg.DebugRunAnalysisOnSelectedEntryPoints != "" {
		nativeBuilder.SetDebugRunAnalysisOnSelectedEntryPoints(cfg.DebugRunAnalysisOnSelectedEntryPoints)
	}

	nativeBuilder.SetJarPath(analyzerJarPath)
	for _, classDir := range dataflowClassDirs {
		nativeBuilder.AddDataflowApproximations(classDir)
	}

	analyzerJavaRunner := newAnalyzerJavaRunner()
	if _, err := analyzerJavaRunner.EnsureJava(); err != nil {
		fail("Failed to find Java for the analyzer", err)
	}

	// A report left by an earlier scan would pass for the result of this one when the analyzer
	// fails before it writes a report.
	if err := utils.RemoveIfExists(absSarifReportPath); err != nil {
		fail("Failed to remove the old SARIF report", err)
	}

	var analyzerFail *analyzer.Error
	var scanCmdErr *java.JavaCommandError
	// The spinner shows a failed analyzer run as failed, and the error is printed below.
	if err := out.RunWithSpinner("Analyzing project", func() error {
		var scanErr error
		scanCmdErr, scanErr = scanProject(nativeBuilder, analyzerJavaRunner)
		if scanErr == nil && scanCmdErr != nil {
			return scanCmdErr
		}
		return scanErr
	}); err != nil && scanCmdErr == nil {
		fail("Failed to run the analyzer", err)
	}
	if analyzerFail = analyzer.Classify(scanCmdErr); analyzerFail != nil {
		out.Errorf("%s", analyzerFail.Message)
	}

	report, err := validation.ValidateSarifOutput(absSarifReportPath)
	if err != nil {
		output.LogInfof("Scan output validation failed: %v", err)
		if analyzerFail == nil {
			// Analyzer reported success but produced no valid SARIF — treat as failure.
			out.Error("The analyzer wrote no valid SARIF report", err)
			analyzerFail = &analyzer.Error{ExitCode: 1, Message: "scan output validation failed"}
		}
	}

	el, err := validation.ValidateRuleLoadTraceOutput(absSemgrepRuleLoadTracePath)
	if report != nil || el != nil {
		out.Blank()
	}
	if err != nil {
		output.LogInfof("Rule load trace validation failed: %v", err)
		if analyzerFail == nil {
			out.Error("Failed to read the rule load trace", err)
			analyzerFail = &analyzer.Error{ExitCode: 1, Message: "rule load trace validation failed"}
		}
	}

	var ruleLoadIssues load_trace.RuleLoadIssues
	if el != nil {
		rulesetPaths := make([]string, 0, len(absRuleSetPaths))
		for _, r := range absRuleSetPaths {
			rulesetPaths = append(rulesetPaths, r.Path)
		}
		ruleLoadIssues = load_trace.CollectRuleLoadIssues(el, rulesetPaths)
		ruleLoadIssues.Print(out)
	}

	var suggestions []output.Suggestion
	if analyzerFail != nil {
		suggestions = appendLogSuggestion(suggestions)
		if analyzerLog, ok := analyzerLogSuggestion(analyzerFail, nativeBuilder.LogsFile()); ok {
			suggestions = append(suggestions, analyzerLog)
		}
		if retry, ok := retrySuggestion(analyzerFail.ExitCode, globals.Config.Scan.Timeout, globals.Config.Scan.MaxMemory); ok {
			suggestions = append(suggestions, retry)
		}
	}
	if report != nil {
		// Scan does not expose summary's filter/group flags, so pass zero values:
		// no filtering, default group dimension, first-flow code-flow selection.
		var extraOutputs []any
		reachabilityTracePath := filepath.Join(filepath.Dir(absSarifReportPath), "debug-ifds-fact-reachability.sarif")
		if cfg.DebugFactReachabilitySarif && utils.PathExists(reachabilityTracePath) {
			extraOutputs = append(extraOutputs, out.FieldItem("Reachability trace", reachabilityTracePath))
		}
		if el != nil && (!ruleLoadIssues.Empty() || globals.Config.Output.Debug) {
			extraOutputs = append(extraOutputs, out.FieldItem("Rule load trace", absSemgrepRuleLoadTracePath))
		}
		if el != nil {
			// The Rule Loading block is above.
			out.Blank()
		}
		printSarifSummary(report, absSarifReportPath, sarif.Filters{}, sarif.ListingOptions{MaxNestingLevel: -1}, extraOutputs...)
		switch {
		case cfg.DebugFactReachabilitySarif:
			if analyzerFail == nil {
				out.Blank()
				out.Successf("Reachability analysis completed")
			}
		case sarif.GenerateSummary(report).TotalFindings > 0:
			if analyzerFail == nil {
				out.Blank()
				out.Successf("Scan completed")
			}
			suggestions = append(suggestions, output.Suggestion{
				Description: "To view the findings, run:",
				Command:     utils.NewSummaryCommand(absSarifReportPath).WithShowFindings().Build(),
			})
		case analyzerFail == nil:
			out.Blank()
			out.Successf("Scan completed with no %s findings", strings.Join(cfg.Severity, " or "))
			if isDefaultSeverity(cfg.Severity) {
				suggestions = append(suggestions, output.Suggestion{
					Description: "To also check note-level rules, run:",
					Command:     noteSeverityScanCommand(cfg),
				})
			}
		}
	}
	out.Suggestions(suggestions...)

	if analyzerFail != nil {
		os.Exit(analyzerFail.ExitCode)
	}
}

// noteSeverityScanCommand returns the scan that also runs the note-level rules. It keeps the
// default severities, so that its report holds every finding of this scan too.
func noteSeverityScanCommand(cfg ScanConfig) string {
	sourcePath := cfg.UserProjectPath
	if cfg.ProjectModelPath != "" {
		sourcePath = ""
	}
	b := currentScanBuilder(cfg, sourcePath).WithSeverity([]string{"note", "warning", "error"})
	if cfg.ProjectModelPath != "" {
		b.WithProjectModel(cfg.ProjectModelPath)
	}
	return b.Build()
}

func resolveScanPlan(cfg ScanConfig, absUserProjectRoot string) scanPlan {
	if cfg.ProjectModelPath != "" {
		return scanPlan{
			absProjectModel: log.AbsPathOrExit(filepath.Clean(cfg.ProjectModelPath), "project model path"),
		}
	}

	if cfg.DryRun {
		dryRunPath := filepath.Join(os.TempDir(), dryRunScanProjectModelPath)
		return scanPlan{
			absProjectModel:  dryRunPath,
			needsCompilation: true,
		}
	}

	projectCachePath, err := utils.GetProjectCachePath(absUserProjectRoot)
	if err != nil {
		out.Fatal("Failed to create the project model cache", err)
	}

	cachedModelPath := utils.CachedProjectModelPath(projectCachePath)
	cacheLockPath := utils.CacheLockPath(projectCachePath)

	// Fast path: if we're not forced to recompile and the cache looks
	// complete on disk, take a shared lock and re-check under the lock.
	if !cfg.Recompile && utils.IsCachedModelComplete(projectCachePath) {
		sharedLock, sharedErr := utils.TryLockShared(cacheLockPath)
		if sharedErr == nil {
			if utils.IsCachedModelComplete(projectCachePath) {
				output.LogDebugf("Reusing cached model at: %s", cachedModelPath)
				return scanPlan{
					absProjectModel:  cachedModelPath,
					projectCachePath: projectCachePath,
					cacheLock:        sharedLock,
				}
			}
			// Marker vanished between the outer check and the lock
			// (writer raced ahead of us). Fall through to compile path.
			sharedLock.Unlock()
		} else if sharedErr != utils.ErrLocked {
			out.Fatal("Failed to lock the project model cache", sharedErr)
		}
		// sharedErr == ErrLocked means a writer holds the cache; we're about
		// to ask for exclusive below, which will also fail with ErrLocked —
		// ReadLockMeta below will surface which command is holding it.
	}

	cacheLock, lockErr := utils.TryLockExclusive(
		cacheLockPath,
		utils.LockMeta{PID: os.Getpid(), Command: "compile", Project: absUserProjectRoot},
	)
	if lockErr == utils.ErrLocked {
		// Readers don't stamp metadata (empty LockMeta); writers do. Use that
		// to distinguish an in-progress compile from an in-progress analyze.
		if meta, _ := utils.ReadLockMeta(cacheLockPath); meta.PID != 0 {
			out.Fatalf("Another command is compiling this project")
		}
		out.Fatalf("Another scan is analyzing this project")
	}
	if lockErr != nil {
		out.Fatal("Failed to lock the project model cache", lockErr)
	}

	return scanPlan{
		absProjectModel:  cachedModelPath,
		projectCachePath: projectCachePath,
		needsCompilation: true,
		cacheLock:        cacheLock,
	}
}

func printScanInfo(cmd *cobra.Command, plan scanPlan, absSemgrepRuleLoadTracePath string, absUserProjectRoot string, absRuleSetPaths []RulesetType) {
	sb := out.Section(plan.title())
	addConfigFields(cmd, sb)
	if globals.Config.Output.Debug {
		sb.FieldNode("Rule load trace", absSemgrepRuleLoadTracePath)
		sb.Line()
	}
	if plan.needsCompilation {
		sb.FieldNode("Project", absUserProjectRoot)
		if plan.projectCachePath != "" {
			sb.FieldNode("Project model", plan.absProjectModel)
		}
		sb.FieldGroup("Autobuilder", componentItems(resolveJarComponent("autobuilder"), false)...)
	} else {
		sb.FieldNode("Project model", plan.absProjectModel)
	}
	sb.FieldGroup("Analyzer", componentItems(resolveJarComponent("analyzer"), false)...)
	for _, r := range absRuleSetPaths {
		if r.Builtin {
			rules := healthComponent{
				version: utils.ArtifactVersion(globals.ArtifactByKind("rules")),
				path:    r.Path,
				present: utils.PathExists(r.Path),
			}
			sb.FieldGroup("Built-in ruleset", componentItems(rules, false)...)
		} else {
			sb.FieldNode("Custom ruleset", r.Path)
		}
	}
	sb.Render()
}

func setupSemgrepRuleLoadTrace(traceDir string) string {
	absSemgrepRuleLoadTracePath, err := load_trace.RuleLoadTracePathIn(traceDir)
	if err != nil {
		out.Fatal("Failed to prepare the rule load trace", err)
	}

	if err = utils.RemoveIfExists(absSemgrepRuleLoadTracePath); err != nil {
		out.Fatal(fmt.Sprintf("Failed to remove the old rule load trace `%s`", absSemgrepRuleLoadTracePath), err)
	}

	// Rule load trace path is now displayed in the tree format
	return absSemgrepRuleLoadTracePath
}

func scanProject(analyzerBuilder *AnalyzerBuilder, javaRunner java.JavaRunner) (*java.JavaCommandError, error) {
	analyzerCommand := analyzerBuilder.BuildNativeCommand()

	commandSucceeded := func(err error) bool {
		if err != nil {
			output.LogDebugf("Analyzer failed: %v", err)
			return false
		}
		return true
	}

	return javaRunner.ExecuteJavaCommand(analyzerCommand, commandSucceeded)
}
