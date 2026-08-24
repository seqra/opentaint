package cmd

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"slices"
	"strings"
	"time"

	"github.com/seqra/opentaint/internal/analyzer"
	"github.com/seqra/opentaint/internal/load_trace"
	"github.com/seqra/opentaint/internal/rules"
	"github.com/seqra/opentaint/internal/sarif"
	"github.com/seqra/opentaint/internal/triage"
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
	ExcludeRuleID             []string
	PassthroughApproximations []string
	DataflowApproximations    []string
	TrackExternalMethods      bool

	Baseline           string
	WriteBaselineState bool
	ErrorOnFindings    bool
	ErrorOnSeverity    []string

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
	Short: "Scan a project for vulnerabilities",
	Args:  cobra.MaximumNArgs(1),
	Long: `Scan a project and find vulnerabilities. OpenTaint finds the build system, builds the project, and does a taint analysis.

The source-path argument is the project root. It is optional. The default is the current directory. To scan a project model that is already compiled, use --project-model. Do not give source-path and --project-model together.

OpenTaint writes the findings to a SARIF report. Use --output to set the report path. If --output is not set, the report goes into the project model directory. A summary is shown when the scan completes.

To compare with a previous report, use --baseline. The scan then keeps the suppressions from the baseline. With --error-on-findings, only new findings that are not suppressed cause a failure. To record decisions about findings, use "opentaint triage".

Before your first scan, run "opentaint pull" one time. For a Go project, the "go" command must also be on your PATH. To read a report again later, use "opentaint summary".

` + gateExitCodesHelp("Scan completed"),
	Example: `  # Scan the current directory with the built-in rules
  opentaint scan .

  # Scan a project and write the report to a known path
  opentaint scan ./my-app -o report.sarif

  # Scan a project model that is already compiled
  opentaint scan --project-model ./model -o report.sarif

  # Use your own rules and show only errors
  opentaint scan . --ruleset ./rules --severity error -o report.sarif

  # Fail CI only on findings that are new since the baseline
  opentaint scan . --baseline main.sarif --error-on-findings -o report.sarif

  # Give a large project more time and memory
  opentaint scan . --timeout 30m --max-memory 16G -o report.sarif

  # Recipe: first scan on a new machine
  opentaint pull
  opentaint scan . -o report.sarif
  opentaint summary report.sarif --show-findings

  # Recipe: build one time, then scan many times
  opentaint compile ./my-app -o ./model
  opentaint scan --project-model ./model -o report.sarif

  # Recipe: a CI gate that fails only on new findings
  opentaint scan . --baseline baselines/main.sarif --error-on-findings -o report.sarif
  opentaint summary report.sarif --baseline baselines/main.sarif --baseline-state new --show-findings`,
	Annotations: map[string]string{"PrintConfig": "true"},
	Run: func(cmd *cobra.Command, args []string) {
		runScan(cmd, prepareScanConfig(scanFlags, args))
	},
}

func prepareScanConfig(cfg ScanConfig, args []string) ScanConfig {
	if len(args) > 0 && cfg.ProjectModelPath != "" {
		out.Error("Cannot use both a source path argument and --project-model flag")
		suggest("Use either a source path or --project-model:",
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
	cmd.Flags().StringArrayVar(&scanFlags.RuleID, "rule-id", nil, "Run only rules with this ID (repeatable)")
	cmd.Flags().StringArrayVar(&scanFlags.ExcludeRuleID, "exclude-rule-id", nil, "Never run rules matching this ID: full id, bare name, or glob over the full id (repeatable, overrides rules.exclude from the config)")
}

func addScanFlags(cmd *cobra.Command) {
	cmd.Flags().DurationVarP(&globals.Config.Scan.Timeout, "timeout", "t", 900*time.Second, "Maximum wall-clock time for analysis (e.g. 30m, 1h)")

	cmd.Flags().StringArrayVar(&scanFlags.Ruleset, "ruleset", []string{"builtin"}, "Rules to run: a YAML file, a directory of .yml or .yaml files, or builtin for the built-in rules (repeatable)")

	cmd.Flags().BoolVar(&scanFlags.SemgrepCompatibilitySarif, "semgrep-compatibility-sarif", true, "Use Semgrep-compatible rule IDs in the SARIF report")
	cmd.Flags().StringVarP(&scanFlags.SarifReportPath, "output", "o", "", "Path to write the SARIF report")

	cmd.Flags().StringArrayVar(&scanFlags.Severity, "severity", []string{"warning", "error"}, "Run only rules at these severity levels: note, warning, error (repeatable)")
	cmd.Flags().StringVar(&globals.Config.Scan.MaxMemory, "max-memory", "8G", "Maximum analyzer heap size (e.g. 8G, 1024m)")
	cmd.Flags().Int64Var(&globals.Config.Scan.CodeFlowLimit, "code-flow-limit", 0, "Maximum number of code flows to include in the report (0 = unlimited)")
	cmd.Flags().BoolVar(&scanFlags.DryRun, "dry-run", false, "Validate inputs and show what would run without compiling or scanning")
	cmd.Flags().BoolVar(&scanFlags.Recompile, "recompile", false, "Force recompilation even if a cached project model exists")
	cmd.Flags().StringVar(&scanFlags.ProjectModelPath, "project-model", "", "Path to a pre-compiled project model (skips compilation)")
	cmd.Flags().StringVar(&scanFlags.LogFile, "log-file", "", "Path to the log file (default: <cache-dir>/logs/<timestamp>.log)")

	addRenamedStringArrayFlag(cmd.Flags(), &scanFlags.PassthroughApproximations, "passthrough-models", "passthrough-approximations", "Pass-through models: a YAML file or a directory of them (repeatable)")

	addRenamedStringArrayFlag(cmd.Flags(), &scanFlags.DataflowApproximations, "java-models", "dataflow-approximations", "Java dataflow models: a compiled class directory or a Java source directory (repeatable)")

	cmd.Flags().BoolVar(&scanFlags.TrackExternalMethods, "track-external-methods", false, "Write external-method coverage files next to the SARIF report")

	addBaselineFlags(cmd, &scanFlags.Baseline)
	cmd.Flags().BoolVar(&scanFlags.WriteBaselineState, "write-baseline-state", false, "Persist result.baselineState and run.baselineGuid into the output report (needs --baseline)")
	addGateFlags(cmd, &scanFlags.ErrorOnFindings, &scanFlags.ErrorOnSeverity)
}

// currentScanBuilder returns a builder pre-populated with the user's current scan flags.
func currentScanBuilder(cfg ScanConfig, sourcePath string) *utils.OpentaintCommandBuilder {
	b := utils.NewScanCommand(sourcePath).
		WithOutput(cfg.SarifReportPath).
		WithTimeout(globals.Config.Scan.Timeout).
		WithRuleset(cfg.Ruleset).
		WithSemgrepCompatibility(cfg.SemgrepCompatibilitySarif).
		WithRuleID(cfg.RuleID).
		WithExcludeRuleID(cfg.ExcludeRuleID).
		WithPassthroughApproximations(cfg.PassthroughApproximations).
		WithDataflowApproximations(cfg.DataflowApproximations).
		WithTrackExternalMethods(cfg.TrackExternalMethods).
		WithBaseline(cfg.Baseline).
		WithWriteBaselineState(cfg.WriteBaselineState).
		WithErrorOnFindings(cfg.ErrorOnFindings).
		WithErrorOnSeverity(cfg.ErrorOnSeverity)
	if !isDefaultSeverity(cfg.Severity) {
		b.WithSeverity(cfg.Severity)
	}
	return b
}

// resolveRuleIDs determines which rules the analyzer should run, as exact
// inclusion and exclusion ids (patterns never reach the analyzer).
//
// --rule-id wins over the config lists, as flags do everywhere else. Honoring
// a flag and rules.only together would silently intersect two selections the
// user never asked to combine. --exclude-rule-id overrides rules.exclude the
// same way, and composes with --rule-id since both were asked for explicitly.
// Returns the zero value when nothing restricts the rules, which runs the
// whole ruleset.
func resolveRuleIDs(cfg ScanConfig, absRuleSetPaths []RulesetType) rules.Resolved {
	var rulesetRoots []string
	for _, r := range absRuleSetPaths {
		rulesetRoots = append(rulesetRoots, r.Path)
	}

	if len(cfg.RuleID) > 0 {
		// The explicit list is small, so exclusions are subtracted right here
		// and the analyzer sees only the survivors.
		ids, err := rules.ApplyExclusions(cfg.RuleID, cfg.ExcludeRuleID)
		if err != nil {
			out.Fatalf("%s", err)
		}
		warnUnmatchedRulePatterns(rules.Selection{Exclude: cfg.ExcludeRuleID}, cfg.RuleID)
		if cfg.ExpandRuleRefs {
			ids = rules.ExpandRuleIDs(ids, rulesetRoots)
		}
		return rules.Resolved{Include: ids}
	}

	selection := configuredRuleSelection(cfg)
	selected, err := rules.Select(selection, rulesetRoots)
	if err != nil {
		out.Fatalf("%s", err)
	}
	if selection.Active() {
		warnUnmatchedRulePatterns(selection, rules.ListRuleIDs(rulesetRoots))
	}
	return selected
}

// warnUnmatchedRulePatterns surfaces selection patterns that matched no rule.
// A pattern matching nothing is usually a typo, and staying silent would make
// an exclusion look effective when it never was.
func warnUnmatchedRulePatterns(selection rules.Selection, all []string) {
	for _, pattern := range selection.Unmatched(all) {
		out.Warnf("Rule pattern %q matches no rule in the active ruleset", pattern)
	}
}

// configuredRuleSelection merges the rules.only / rules.exclude lists from the
// configuration file with the --exclude-rule-id flag, which overrides the
// configured exclude list when set.
// ruleSelectionActive reports whether any rule allow/deny input is in play —
// the flags or the config lists. Only then does rule resolution read the
// ruleset from disk.
func ruleSelectionActive(cfg ScanConfig) bool {
	return len(cfg.RuleID) > 0 || len(cfg.ExcludeRuleID) > 0 || configuredRuleSelection(cfg).Active()
}

func configuredRuleSelection(cfg ScanConfig) rules.Selection {
	selection := rules.Selection{
		Only:    globals.Config.Rules.Only,
		Exclude: globals.Config.Rules.Exclude,
	}
	if len(cfg.ExcludeRuleID) > 0 {
		selection.Exclude = cfg.ExcludeRuleID
	}
	return selection
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
		out.Fatalf("Unsupported architecture found: %s! Only arm64 and amd64 are supported.", utils.GetArch())
	}

	// When compiling from sources, validate the source folder looks like a Java/Kotlin project
	if cfg.ProjectModelPath == "" {
		if err := validation.ValidateSourceProject(absUserProjectRoot); err != nil {
			if validation.IsProjectModel(absUserProjectRoot) {
				out.ErrorErr(err)
				suggest("Use --project-model to scan a pre-compiled model:", currentScanBuilder(cfg, "").WithProjectModel(absUserProjectRoot).Build())
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

	// Validate the triage flags before compiling: a typo in --baseline should
	// not surface only after a fifteen-minute analysis.
	gateSeverities, err := triage.ParseGateSeverities(cfg.ErrorOnSeverity)
	if err != nil {
		out.Fatalf("%s", err)
	}
	if cfg.WriteBaselineState && cfg.Baseline == "" {
		out.Fatalf("--write-baseline-state needs a --baseline to compare against")
	}
	var baseline *sarif.Report
	var absBaselinePath string
	if cfg.Baseline != "" {
		baseline, absBaselinePath = loadBaselineOrExit(cfg.Baseline, absSarifReportPath)
		if err := sarif.CheckBaselineIdentity(baseline); err != nil {
			out.Fatalf("%s", err)
		}
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

	hasBuiltin := false
	for _, ruleSetPath := range absRuleSetPaths {
		if ruleSetPath.Builtin {
			hasBuiltin = true
			break
		}
	}

	// Rule selections resolve against the rule files on disk, so the built-in
	// rules must be fetched before an active selection is resolved — a fresh
	// install has not downloaded them yet.
	if hasBuiltin && ruleSelectionActive(cfg) {
		if _, err := utils.EnsureRulesPath(out); err != nil {
			failf("Failed to prepare built-in rules: %s", err)
		}
	}

	// Resolve the active rules before the dry-run bail-out, so that a bad
	// rules.only/rules.exclude list is reported by --dry-run and never after a
	// full compile.
	resolvedRules := resolveRuleIDs(cfg, absRuleSetPaths)

	if cfg.DryRun {
		runDryRun("the build and scan")
		return
	}

	// Go projects: the analyzer starts a go-ssa-server process, and that server
	// runs the `go` toolchain. The decision about the Go wiring occurs here,
	// after the --dry-run return and before the compile and the analyzer
	// download. Thus a dry run causes no side effects, and a Go-only scan with
	// no `go` toolchain fails fast, not after a long compile.
	//
	// For a source scan, sourceRoot is the live source tree. For a
	// --project-model scan, it is the sourceRoot from project.yaml. Thus the
	// detection covers both paths. For a precompiled model, the recorded source
	// root must still exist on disk with its go.mod. If it does not, the
	// detection finds no languages.
	//
	// The `go` preflight does not depend on the --go-server-binary override,
	// because go-ssa-server always runs `go`. It applies when Go is detected.
	// If Go is the only language, the command stops with an error. If other
	// languages are present, the command shows a warning and does not do the
	// Go wiring. The resolution of the binary occurs later (see
	// resolveGoServerEnv), after the compile. Thus a missing `go` is reported
	// before the long compile runs.
	needGoServer := goServerRequired(sourceRoot)

	if hasBuiltin {
		if _, err := utils.EnsureRulesPath(out); err != nil {
			failf("Failed to prepare built-in rules: %s", err)
		}
	}

	if plan.needsCompilation {
		autobuilderJarPath, err := ensureAutobuilderAvailable()
		if err != nil {
			failf("Native compile preparation failed: %s", err)
		}

		compileJavaRunner := newAutobuilderJavaRunner()
		if _, err := compileJavaRunner.EnsureJava(); err != nil {
			failf("Failed to resolve Java for compilation: %s", err)
		}

		// Wipe any residue from a prior crashed compile before writing new output.
		if plan.projectCachePath != "" {
			if err := os.RemoveAll(plan.absProjectModel); err != nil {
				failf("Failed to prepare cache directory: %s", err)
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
				failf("Failed to mark model complete: %s", err)
			}
			if err := plan.cacheLock.Downgrade(); err != nil {
				output.LogInfof("Cache lock downgrade failed, continuing under exclusive: %v", err)
			}
		}

		printCompileSummary(absProjectModelPath)
	}

	if err := utils.EnsureParentDir(absSarifReportPath); err != nil {
		failf("Failed to create output directory: %s", err)
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
	for _, ruleID := range resolvedRules.Include {
		nativeBuilder.AddRuleID(ruleID)
	}
	for _, ruleID := range resolvedRules.Exclude {
		nativeBuilder.AddRuleIDExclude(ruleID)
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
		failf("Native scan preparation failed: %s", err)
	}
	nativeBuilder.SetJarPath(analyzerJarPath)

	// Process --java-models: auto-compile .java sources if needed
	addDataflowApproximations(nativeBuilder, cfg.DataflowApproximations, analyzerJarPath, absProjectModelPath)

	// Go projects: get the go-ssa-server binary (a download, or the
	// --go-server-binary override) and give its absolute path to the analyzer
	// in GOIR_SERVER_BINARY. The needGoServer decision occurred early, after
	// the --dry-run return, where the `go` preflight ran. This block only
	// resolves the binary and sets the env. A scan with no Go, and a polyglot
	// scan where `go` was missing, keep goServerEnv nil. Then
	// WithExtraEnv(nil) does nothing and those runs do not change.
	var goServerEnv map[string]string
	if needGoServer {
		goServerEnv = resolveGoServerEnv()
	}

	analyzerJavaRunner := newAnalyzerJavaRunner(goServerEnv)
	if _, err := analyzerJavaRunner.EnsureJava(); err != nil {
		failf("Failed to resolve Java for analyzer: %s", err)
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
		if retry, ok := retrySuggestion(analyzerFail.ExitCode, globals.Config.Scan.Timeout, globals.Config.Scan.MaxMemory); ok {
			suggestions = append(suggestions, retry)
		}
	}
	var view *sarif.TriageView
	if report != nil {
		view = triageScanReport(cfg, report, absSarifReportPath, baseline, absBaselinePath)
		// Scan does not expose summary's filter/group flags, so pass zero values:
		// no filtering, default group dimension, first-flow code-flow selection.
		printSarifSummary(report, absSarifReportPath, sarif.Filters{}, sarif.ListingOptions{MaxNestingLevel: -1}, view, false)
		switch {
		case cfg.DebugFactReachabilitySarif:
			if analyzerFail == nil {
				out.Successf("Reachability analysis completed.")
			}
			// The reachability report is the command's deliverable. Point at it,
			// never at the main SARIF.
			reachabilityReportPath := filepath.Join(filepath.Dir(absSarifReportPath), "debug-ifds-fact-reachability.sarif")
			suggestions = append(suggestions, output.Suggestion{
				Description: "To view the reachability report, run:",
				Command:     utils.NewSummaryCommand(reachabilityReportPath).WithShowFindings().Build(),
			})
		case sarif.GenerateSummary(report).TotalFindings > 0:
			if analyzerFail == nil {
				out.Successf("Scan completed.")
			}
			suggestions = append(suggestions, output.Suggestion{
				Description: "To view the findings, run:",
				Command:     utils.NewSummaryCommand(absSarifReportPath).WithShowFindings().Build(),
			})
		case analyzerFail == nil:
			out.Successf("Scan completed. No vulnerabilities found at %s severity.", strings.Join(cfg.Severity, " or "))
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
	if report != nil {
		exitOnGate(triage.Gate{Enabled: cfg.ErrorOnFindings, Severities: gateSeverities}, report, view)
	}
}

// triageScanReport applies the baseline and any inherited suppressions to the
// report the analyzer just wrote, rewriting the file when that changed it. With
// no baseline and no annotation requested, the report is left exactly as the
// analyzer produced it. The baseline was loaded (and validated) before the
// compile step, so a bad path fails fast and the file is read only once.
func triageScanReport(cfg ScanConfig, report *sarif.Report, absSarifReportPath string, baseline *sarif.Report, absBaselinePath string) *sarif.TriageView {
	outcome, err := triage.Apply(report, triage.Options{
		WriteBaselineState: cfg.WriteBaselineState,
		Baseline:           baseline,
		BaselinePath:       absBaselinePath,
	})
	if err != nil {
		out.Fatalf("%s", err)
	}
	if outcome.Changed {
		if err := sarif.SaveReport(report, absSarifReportPath); err != nil {
			out.Fatalf("Failed to write report: %s", err)
		}
	}
	return outcome.View
}

// noteSeverityScanCommand builds the follow-up command for a clean scan: the
// same invocation narrowed to the note-level rules the default run skips.
func noteSeverityScanCommand(cfg ScanConfig) string {
	sourcePath := cfg.UserProjectPath
	if cfg.ProjectModelPath != "" {
		sourcePath = ""
	}
	b := currentScanBuilder(cfg, sourcePath).WithSeverity([]string{"note"})
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
		suggest("To scan an existing model instead, run:", utils.NewScanCommand("").WithProjectModel("<model-path>").Build())
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

// EnsureGoServerAvailable returns the absolute path of the go-ssa-server
// binary. If the binary is absent, the function downloads the asset for this
// platform and, on unix, makes the file executable.
//
// The release tag is the configured go-server version ("go-server/<ver>",
// default globals.GoServerBindVersion). The asset is the platform-specific
// globals.GoServerAssetName() ("go-ssa-server_<GOOS>_<GOARCH>", with ".exe"
// on windows). DownloadGithubReleaseAsset examines the checksums.
//
// This is the public entry point for Go projects and for "opentaint pull".
// The function does not set environment variables.
//
// The --go-server-binary override (globals.Config.GoServer.Binary) has
// priority. With it, the function makes sure that the given path exists,
// converts the path to an absolute path, and returns it. No download, no
// version tag, and no chmod occur. The user-supplied file does not change.
// This is the same behavior as the --analyzer-jar override in
// ensureAnalyzerAvailable().
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

// goServerRequired reports whether the analyzer needs the go-ssa-server for
// the project at sourceRoot. As a side effect, it does the `go` toolchain
// preflight. If Go is present but `go` is missing, a Go-only project causes
// an error, and a polyglot project causes a warning and a false result. The
// preflight does not depend on the --go-server-binary override, because
// go-ssa-server always runs `go`. If Go is absent, the result is false.
//
// This function is the "decide" half of the Go wiring, and resolveGoServerEnv
// is the "resolve" half. The scan command keeps the two apart. Thus the
// preflight can run before the autobuilder compile (fail fast) and the
// download after it. A caller with no compile step (for example, the rule
// tests) calls the two functions one after the other.
func goServerRequired(sourceRoot string) bool {
	langs := validation.DetectLanguages(sourceRoot)
	if !slices.Contains(langs, "Go") {
		return false
	}
	if _, lookErr := exec.LookPath("go"); lookErr != nil {
		if len(langs) == 1 {
			out.Fatal("A Go project needs the Go toolchain, but `go` was not found on your PATH.\n" +
				"Install Go (https://go.dev/dl/), make sure `go` is on your PATH, and run the command again.")
		}
		out.Warnf("A Go module (go.mod) was found, but `go` is not on your PATH. " +
			"The scan continues with the other detected languages and does not analyze the Go code. " +
			"To analyze Go, install Go (https://go.dev/dl/).")
		return false
	}
	return true
}

// resolveGoServerEnv gets the go-ssa-server binary (a download, or the
// --go-server-binary override) and returns the analyzer env that points
// GOIR_SERVER_BINARY at its absolute path. Call it only when
// goServerRequired returned true.
func resolveGoServerEnv() map[string]string {
	goServerPath, err := EnsureGoServerAvailable()
	if err != nil {
		out.Fatalf("Failed to resolve go-ssa-server: %s", err)
	}
	return map[string]string{"GOIR_SERVER_BINARY": goServerPath}
}

// goServerEnvForModel does goServerRequired and then resolveGoServerEnv for
// a compiled project model. It reads the source root that the model recorded.
// It returns the go-ssa-server env when the model needs it, and nil when not.
// The result goes directly to newAnalyzerJavaRunner, where WithExtraEnv(nil)
// does nothing.
func goServerEnvForModel(projectModelPath string) map[string]string {
	sourceRoot, err := project.GetSourceRoot(projectModelPath)
	if err != nil {
		out.Fatalf("Failed to parse sourceRoot from project.yaml: %v", err)
	}
	if !goServerRequired(sourceRoot) {
		return nil
	}
	return resolveGoServerEnv()
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
