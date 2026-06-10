package cmd

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"slices"
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
	PassthroughApproximations []string
	DataflowApproximations    []string
	TrackExternalMethods      bool

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
	Use:   "scan [source-path]",
	Short: "Scan your Java or Kotlin project",
	Args:  cobra.MaximumNArgs(1),
	Long: `This command automatically detects Java/Kotlin build systems, builds the project, and analyzes it

Arguments:
  source-path  - Path to the project sources (default: current directory)

Use --project-model to scan a pre-compiled project model instead of compiling from sources.
`,
	Annotations: map[string]string{"PrintConfig": "true"},
	Run: func(cmd *cobra.Command, args []string) {
		runScan(cmd, prepareScanConfig(scanFlags, args))
	},
}

func prepareScanConfig(cfg ScanConfig, args []string) ScanConfig {
	if len(args) > 0 && cfg.ProjectModelPath != "" {
		out.Error("Cannot use both a source path argument and --project-model flag")
		suggest("Use either a source path or --project-model",
			utils.NewScanCommand("<source-path>").Build()+"\n  "+utils.NewScanCommand("").WithProjectModel("<model-path>").Build())
		os.Exit(1)
	}
	if cfg.Recompile && cfg.ProjectModelPath != "" {
		out.Fatalf("Cannot use --recompile with --project-model; the flag only applies when compiling from sources")
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
}

func addRuleIDFlag(cmd *cobra.Command) {
	cmd.Flags().StringArrayVar(&scanFlags.RuleID, "rule-id", nil, "Filter active rules by ID (repeatable)")
}

func addScanFlags(cmd *cobra.Command) {
	cmd.Flags().DurationVarP(&globals.Config.Scan.Timeout, "timeout", "t", 900*time.Second, "Timeout for analysis")

	cmd.Flags().StringArrayVar(&scanFlags.Ruleset, "ruleset", []string{"builtin"}, "YAML rules file, directory of YAML rules files ending in .yml or .yaml, or `builtin` to scan with built-in rules")

	cmd.Flags().BoolVar(&scanFlags.SemgrepCompatibilitySarif, "semgrep-compatibility-sarif", true, "Use Semgrep compatible ruleId")
	cmd.Flags().StringVarP(&scanFlags.SarifReportPath, "output", "o", "", "Path to the SARIF-report output file")

	cmd.Flags().StringArrayVar(&scanFlags.Severity, "severity", []string{"warning", "error"}, "Report findings only from rules matching the supplied severity level. By default only warning and error rules are run (note, warning, error)")
	cmd.Flags().StringVar(&globals.Config.Scan.MaxMemory, "max-memory", "8G", "Maximum memory for the analyzer (e.g., 1024m, 8G, 81920k, 83886080)")
	cmd.Flags().Int64Var(&globals.Config.Scan.CodeFlowLimit, "code-flow-limit", 0, "Maximum number of code flows to include in the report (0 = unlimited)")
	cmd.Flags().BoolVar(&scanFlags.DryRun, "dry-run", false, "Validate inputs and show what would run without compiling or scanning")
	cmd.Flags().BoolVar(&scanFlags.Recompile, "recompile", false, "Force recompilation even if a cached project model exists")
	cmd.Flags().StringVar(&scanFlags.ProjectModelPath, "project-model", "", "Path to a pre-compiled project model (skips compilation)")
	cmd.Flags().StringVar(&scanFlags.LogFile, "log-file", "", "Path to the log file (default: <cache-dir>/logs/<timestamp>.log)")

	cmd.Flags().StringArrayVar(&scanFlags.PassthroughApproximations, "passthrough-approximations", nil, "Pass-through approximation YAML file or directory (repeatable)")

	cmd.Flags().StringArrayVar(&scanFlags.DataflowApproximations, "dataflow-approximations", nil, "Dataflow approximation class directory or Java source directory (repeatable)")

	cmd.Flags().BoolVar(&scanFlags.TrackExternalMethods, "track-external-methods", false, "Write external-method coverage files next to the SARIF report")
}

// currentScanBuilder returns a builder pre-populated with the user's current scan flags.
func currentScanBuilder(cfg ScanConfig, sourcePath string) *utils.OpentaintCommandBuilder {
	b := utils.NewScanCommand(sourcePath).
		WithOutput(cfg.SarifReportPath).
		WithTimeout(globals.Config.Scan.Timeout).
		WithRuleset(cfg.Ruleset).
		WithSemgrepCompatibility(cfg.SemgrepCompatibilitySarif).
		WithRuleID(cfg.RuleID).
		WithPassthroughApproximations(cfg.PassthroughApproximations).
		WithDataflowApproximations(cfg.DataflowApproximations).
		WithTrackExternalMethods(cfg.TrackExternalMethods)
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
		Description: dockerFallbackHintPrefix + "scan:",
		Command:     utils.BuildScanCommandWithDocker(currentScanBuilder(cfg, ""), projectRoot, sarifReportPath, cfg.Ruleset),
	}
}

func runScan(cmd *cobra.Command, cfg ScanConfig) {
	userProjectPath := filepath.Clean(cfg.UserProjectPath)
	absUserProjectRoot := log.AbsPathOrExit(userProjectPath, "project path")

	if !utils.IsSupportedArch() {
		out.Fatalf("Unsupported architecture found: %s! Only arm64 and amd64 are supported.", utils.GetArch())
	}

	// When compiling from sources, validate the source folder looks like a Java/Kotlin project
	if cfg.ProjectModelPath == "" {
		if err := validation.ValidateSourceProject(absUserProjectRoot); err != nil {
			if validation.IsProjectModel(absUserProjectRoot) {
				out.ErrorErr(err)
				suggest("Use --project-model to scan a pre-compiled model", currentScanBuilder(cfg, "").WithProjectModel(absUserProjectRoot).Build())
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
				out.Fatalf("Unexpected error occurred while trying to construct path to the ruleset: %s", err)
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
	} else {
		absSarifReportPath = utils.DefaultSarifReportPath(absProjectModelPath)
	}

	sarifReportName := filepath.Base(absSarifReportPath)

	localVersion := utils.ArtifactDisplayVersion(globals.ArtifactByKind("analyzer"))
	localSemanticVersion := version.GetVersion()

	var sourceRoot string
	if !plan.needsCompilation {
		if parsedSourceRoot, err := project.GetSourceRoot(absProjectModelPath); err != nil {
			out.Fatalf("Failed to parse sourceRoot from project.yaml: %v", err)
		} else {
			sourceRoot = parsedSourceRoot
		}
	} else {
		sourceRoot = absUserProjectRoot
	}

	uriBase := fmt.Sprintf("%s%s", sourceRoot, string(filepath.Separator))

	ruleLoadTraceDir, err := utils.GetProjectLogPath(absUserProjectRoot)
	if err != nil {
		out.Fatalf("Failed to resolve rule load trace directory: %v", err)
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
		out.Fatalf("Input validation failed: %s", err)
	}

	if cfg.DryRun {
		runDryRun("Compilation and analysis")
		return
	}


	// Go projects: the analyzer drives an out-of-process go-ssa-server, which in
	// turn shells out to the `go` toolchain at runtime. Decide the Go wiring up
	// front — after the --dry-run early return (so dry-run stays side-effect-free)
	// and BEFORE the autobuilder compile + analyzer download — so a Go-only scan
	// with a missing `go` toolchain fails fast rather than after a long compile.
	//
	// sourceRoot is the live source tree for source scans and the project.yaml
	// sourceRoot for --project-model scans, so detection covers both paths; for a
	// precompiled model it relies on the recorded source root still existing on
	// disk with its go.mod (otherwise detection yields no languages).
	//
	// The `go` preflight is INDEPENDENT of the --go-server-binary override
	// (go-ssa-server still shells out to `go`), so it applies whenever Go is
	// detected. When Go is the SOLE language we hard-fail; when other languages are
	// also present we warn and skip Go wiring rather than failing the whole scan.
	needGoServer := false
	langs := validation.DetectLanguages(sourceRoot)
	if slices.Contains(langs, "Go") {
		if _, lookErr := exec.LookPath("go"); lookErr != nil {
			if len(langs) == 1 {
				out.Fatal("Scanning a Go project requires the Go toolchain, but `go` was not found on your PATH.\n" +
					"Install Go (https://go.dev/dl/) and ensure `go` is on your PATH, then re-run.")
			} else {
				out.Warnf("Detected a Go module (go.mod) but `go` was not found on your PATH; " +
					"skipping Go analysis setup and continuing with the other detected language(s). " +
					"Install Go (https://go.dev/dl/) to enable Go analysis.")
			}
		} else {
			needGoServer = true
		}
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
			out.Fatalf("Failed to prepare built-in rules: %s", err)
		}
	}

	if plan.needsCompilation {
		autobuilderJarPath, err := ensureAutobuilderAvailable()
		if err != nil {
			out.Fatalf("Native compile preparation failed: %s", err)
		}

		compileJavaRunner := newAutobuilderJavaRunner()
		if _, err := compileJavaRunner.EnsureJava(); err != nil {
			out.Fatalf("Failed to resolve Java for compilation: %s", err)
		}

		// Wipe any residue from a prior crashed compile before writing new output.
		if plan.projectCachePath != "" {
			if err := os.RemoveAll(plan.absProjectModel); err != nil {
				out.Fatalf("Failed to prepare cache directory: %s", err)
			}
		}

		if err := out.RunWithSpinner("Compiling project model", func() error {
			return compile(absUserProjectRoot, plan.absProjectModel, autobuilderJarPath, compileJavaRunner)
		}); err != nil {
			if plan.projectCachePath != "" {
				_ = os.RemoveAll(plan.absProjectModel)
			}
			failWith(1, "Native compile has failed: "+err.Error(), dockerScanSuggestion(cfg, absUserProjectRoot, absSarifReportPath))
		}
		out.Blank()

		// Mark the cache as valid, then downgrade to a reader so other scans
		// can run the analyzer against the freshly-compiled model in parallel.
		if plan.projectCachePath != "" {
			if err := utils.MarkCompileComplete(plan.projectCachePath); err != nil {
				_ = os.RemoveAll(plan.absProjectModel)
				out.Fatalf("Failed to mark model complete: %s", err)
			}
			if err := plan.cacheLock.Downgrade(); err != nil {
				output.LogInfof("Cache lock downgrade failed, continuing under exclusive: %v", err)
			}
		}

		printCompileSummary(absProjectModelPath)
	}

	if err := utils.EnsureParentDir(absSarifReportPath); err != nil {
		out.Fatalf("Failed to create output directory: %s", err)
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
	addPassthroughApproximations(nativeBuilder, cfg.PassthroughApproximations)
	if cfg.TrackExternalMethods {
		nativeBuilder.SetTrackExternalMethods(true)
	}
	if cfg.DebugFactReachabilitySarif {
		nativeBuilder.EnableDebugFactReachabilitySarif()
	}
	if cfg.DebugRunAnalysisOnSelectedEntryPoints != "" {
		nativeBuilder.SetDebugRunAnalysisOnSelectedEntryPoints(cfg.DebugRunAnalysisOnSelectedEntryPoints)
	}

	analyzerJarPath, err := ensureAnalyzerAvailable()
	if err != nil {
		out.Fatalf("Native scan preparation failed: %s", err)
	}
	nativeBuilder.SetJarPath(analyzerJarPath)

	// Process --dataflow-approximations: auto-compile .java sources if needed
	addDataflowApproximations(nativeBuilder, cfg.DataflowApproximations, analyzerJarPath, absProjectModelPath)

	// Go projects: resolve the go-ssa-server binary (download, or the
	// --go-server-binary override) and pass its ABSOLUTE path to the analyzer via
	// GOIR_SERVER_BINARY. needGoServer was decided early (after the --dry-run
	// return), where the `go` preflight already ran; here we only do the binary
	// resolution + env injection. Non-Go scans — and polyglot scans where `go` was
	// missing — leave goServerEnv nil, so WithExtraEnv(nil) is a strict no-op and
	// those runs are byte-for-byte unchanged.
	var goServerEnv map[string]string
	if needGoServer {
		goServerPath, goErr := EnsureGoServerAvailable()
		if goErr != nil {
			out.Fatalf("Native scan preparation failed: %s", goErr)
		}
		goServerEnv = map[string]string{"GOIR_SERVER_BINARY": goServerPath}
	}

	analyzerJavaRunner := newAnalyzerJavaRunner(goServerEnv)
	if _, err := analyzerJavaRunner.EnsureJava(); err != nil {
		out.Fatalf("Failed to resolve Java for analyzer: %s", err)
	}

	var analyzerFail *analyzer.Error
	var scanCmdErr *java.JavaCommandError
	if err := out.RunWithSpinner("Analyzing project", func() error {
		var scanErr error
		scanCmdErr, scanErr = scanProject(nativeBuilder, analyzerJavaRunner)
		return scanErr
	}); err != nil {
		failf("Native scan has failed: %s", err)
	}
	if analyzerFail = analyzer.Classify(scanCmdErr); analyzerFail != nil {
		out.Error(analyzerFail.Message)
	}

	report, err := validation.ValidateSarifOutput(absSarifReportPath)
	if err != nil {
		output.LogInfof("Scan output validation failed: %v", err)
		if analyzerFail == nil {
			// Analyzer reported success but produced no valid SARIF — treat as failure.
			out.Error("There was a problem during the scan step")
			analyzerFail = &analyzer.Error{ExitCode: 1, Message: "scan output validation failed"}
		}
	}

	out.Blank()

	el, err := validation.ValidateRuleLoadTraceOutput(absSemgrepRuleLoadTracePath)
	if err != nil {
		output.LogInfof("Rule load trace validation failed: %v", err)
		if analyzerFail == nil {
			out.Error(fmt.Sprintf("Failed to validate rule load trace output: %s", err))
			analyzerFail = &analyzer.Error{ExitCode: 1, Message: "rule load trace validation failed"}
		}
	}

	if el != nil {
		ruleLoadTraceSummary := load_trace.CollectRuleLoadTraceSummary(el, nonBuiltinRulesetPaths)

		res := load_trace.CollectRulesetLoadErrorsSummary(ruleLoadTraceSummary)
		ruleLoadErrorsResult := &res

		var sarifSummary sarif.Summary
		if report != nil {
			sarifSummary = sarif.GenerateSummary(report)
		}
		load_trace.PrintRuleStatisticsTree(out, ruleLoadErrorsResult, absSemgrepRuleLoadTracePath, sarifSummary)

		load_trace.PrintSyntaxErrorReport(out, ruleLoadTraceSummary)
	}

	var suggestions []output.Suggestion
	if analyzerFail != nil {
		suggestions = appendLogSuggestion(suggestions)
	}
	if report != nil {
		// Scan does not expose summary's filter/group flags, so pass zero values:
		// no filtering, default group dimension, first-flow code-flow selection.
		printSarifSummary(report, absSarifReportPath, sarif.Filters{}, sarif.ListingOptions{MaxNestingLevel: -1})
		suggestions = append(suggestions, output.Suggestion{
			Description: "To view findings run",
			Command:     utils.NewSummaryCommand(absSarifReportPath).WithShowFindings().Build(),
		})
	}
	out.Suggestions(suggestions...)

	if analyzerFail != nil {
		os.Exit(analyzerFail.ExitCode)
	}
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
		out.Fatalf("Failed to create model cache directory: %s", err)
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
			out.Fatalf("Failed to acquire cache read lock: %s", sharedErr)
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
			out.Error("Compilation already in progress for this project")
		} else {
			out.Error("Another scan is currently analyzing this project")
		}
		suggest("To scan an existing model instead", utils.NewScanCommand("").WithProjectModel("<model-path>").Build())
		os.Exit(1)
	}
	if lockErr != nil {
		out.Fatalf("Failed to acquire cache lock: %s", lockErr)
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
		sb.FieldNode("Autobuilder", utils.ArtifactVersionWithPath(globals.ArtifactByKind("autobuilder")))
	} else {
		sb.FieldNode("Project model", plan.absProjectModel)
	}
	sb.FieldNode("Analyzer", utils.ArtifactVersionWithPath(globals.ArtifactByKind("analyzer")))
	for _, r := range absRuleSetPaths {
		if r.Builtin {
			sb.FieldNode("Bundled ruleset", utils.ArtifactVersionWithPath(globals.ArtifactByKind("rules")))
		} else {
			sb.FieldNode("User ruleset", r.Path)
		}
	}
	sb.Render()
}

func setupSemgrepRuleLoadTrace(traceDir string) string {
	absSemgrepRuleLoadTracePath, err := load_trace.RuleLoadTracePathIn(traceDir)
	if err != nil {
		out.Fatalf("Failed to generate rule load trace file path: \"%s\": %v", absSemgrepRuleLoadTracePath, err)
	}

	if err = utils.RemoveIfExists(absSemgrepRuleLoadTracePath); err != nil {
		out.Fatalf("Failed to remove existing rule load trace file: \"%s\": %v", absSemgrepRuleLoadTracePath, err)
	}

	// Rule load trace path is now displayed in the tree format
	return absSemgrepRuleLoadTracePath
}

// EnsureGoServerAvailable resolves the go-ssa-server binary path, downloading the
// per-platform asset if absent, makes it executable on unix, and returns its
// ABSOLUTE path.
//
// The release tag is the configured go-server version ("go-server/<ver>", default
// globals.GoServerBindVersion) and the downloaded asset is the platform-specific
// globals.GoServerAssetName() ("go-ssa-server_<GOOS>_<GOARCH>", with ".exe" on
// windows). Checksums are verified automatically by DownloadGithubReleaseAsset.
//
// This is the public entry point intended to be called for Go projects (Task 03)
// and by `opentaint pull`. It does not set any environment variables.
//
// When the --go-server-binary override is set (globals.Config.GoServer.Binary),
// it short-circuits: the provided path is validated to exist, converted to an
// absolute path, and returned WITHOUT downloading, WITHOUT requiring the version
// manifest tag, and WITHOUT chmod (the user-provided file is respected). This
// mirrors how --analyzer-jar overrides ensureAnalyzerAvailable().
func EnsureGoServerAvailable() (string, error) {
	if globals.Config.GoServer.Binary != "" {
		info, err := os.Stat(globals.Config.GoServer.Binary)
		if err != nil {
			return "", fmt.Errorf("go-ssa-server binary not found at %s: %w", globals.Config.GoServer.Binary, err)
		}
		if info.IsDir() {
			return "", fmt.Errorf("go-ssa-server path %s is a directory, expected an executable file", globals.Config.GoServer.Binary)
		}
		if runtime.GOOS != "windows" && info.Mode()&0o111 == 0 {
			return "", fmt.Errorf("go-ssa-server binary %s is not executable (run: chmod +x %s)", globals.Config.GoServer.Binary, globals.Config.GoServer.Binary)
		}
		absPath, err := filepath.Abs(globals.Config.GoServer.Binary)
		if err != nil {
			return "", fmt.Errorf("failed to resolve absolute path to the go-ssa-server: %w", err)
		}
		return absPath, nil
	}

	version := globals.Config.GoServer.Version
	if version == "" {
		version = globals.GoServerBindVersion
	}

	assetName := globals.GoServerAssetName()

	goServerPath, err := utils.GetGoServerPath(version)
	if err != nil {
		return "", fmt.Errorf("failed to construct path to the go-ssa-server: %w", err)
	}

	if err := ensureArtifactAvailable("go-ssa-server", version, goServerPath, func() error {
		return utils.DownloadGithubReleaseAsset(globals.Config.Owner, globals.Config.Repo, version, assetName, goServerPath, globals.Config.Github.Token, globals.Config.SkipVerify, out)
	}); err != nil {
		return "", err
	}

	// The go-ssa-server is a single native binary and must be executable to run.
	if runtime.GOOS != "windows" {
		if err := os.Chmod(goServerPath, 0o755); err != nil {
			return "", fmt.Errorf("failed to mark go-ssa-server executable at %s: %w", goServerPath, err)
		}
	}

	absPath, err := filepath.Abs(goServerPath)
	if err != nil {
		return "", fmt.Errorf("failed to resolve absolute path to the go-ssa-server: %w", err)
	}

	return absPath, nil
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
