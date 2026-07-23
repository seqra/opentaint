package cmd

import (
	"github.com/seqra/opentaint/internal/sarif"
	"github.com/seqra/opentaint/internal/triage"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

// summaryCmd represents the summary command
var summaryCmd = &cobra.Command{
	Use:   "summary <sarif-report>",
	Short: "Show a summary of a SARIF report",
	Args:  cobra.ExactArgs(1), // require exactly one argument
	Long: `Show a summary of a SARIF report in the terminal. The summary counts the findings by severity. It also shows which rules ran and which rules found problems.

The sarif-report argument is the path to a SARIF report. It is required. Use a report from "opentaint scan" or "opentaint test".

To see each finding, use --show-findings. To make the list smaller, use --severity, --rule-id, or --path. To see the full data flow, use --verbose-flow and --show-code-snippets.

This command only reads the report. It does not write files.`,
	Example: `  # Show a summary of a report
  opentaint summary report.sarif

  # Show each finding with its location
  opentaint summary report.sarif --show-findings

  # Show only the error-level findings
  opentaint summary report.sarif --show-findings --severity error

  # Group the findings by rule
  opentaint summary report.sarif --show-findings --group-by rule-id

  # Recipe: examine one rule in full detail
  opentaint summary report.sarif --show-findings --group-by rule-id
  opentaint summary report.sarif --show-findings --rule-id <rule-id> --verbose-flow --show-code-snippets

  # Recipe: read the findings for one part of the code
  opentaint summary report.sarif --show-findings --path "src/main/**" --severity error`,

	Run: func(cmd *cobra.Command, args []string) {
		for _, s := range summarySeverities {
			if err := sarif.ValidateSeverity(s); err != nil {
				out.Fatalf("%s", err)
			}
		}
		dim, err := sarif.ParseGroupDimension(summaryGroupBy)
		if err != nil {
			out.Fatalf("%s", err)
		}
		codeFlowSel, err := sarif.ParseCodeFlowSelection(summaryCodeFlow)
		if err != nil {
			out.Fatalf("%s", err)
		}

		states, err := sarif.ParseBaselineStates(summaryBaselineStates)
		if err != nil {
			out.Fatalf("%s", err)
		}

		absSarifPath := log.AbsPathOrExit(args[0], "sarif path")
		report, err := sarif.LoadReport(absSarifPath)
		if err != nil {
			out.Fatalf("Failed to load SARIF report: %s", err)
		}

		// summary never writes: the baseline comparison and any inherited
		// suppressions are applied to the in-memory copy for display only.
		view := applyTriageForDisplay(report, absSarifPath)

		filters := summaryFilters()
		filters.BaselineStates = states
		printSarifSummary(report, absSarifPath, filters, summaryListingOptions(dim, codeFlowSel), view, showFindings)

		if !showFindings && sarif.GenerateSummary(report.Filter(filters)).TotalFindings > 0 {
			out.Suggest(
				"To list the findings, run:",
				currentSummaryBuilder(absSarifPath).WithShowFindings().Build(),
			)
		}
	},
}

// applyTriageForDisplay runs a read-only triage pass so that summary can show
// baseline states and inherited suppressions without touching the file.
func applyTriageForDisplay(report *sarif.Report, absSarifPath string) *sarif.TriageView {
	if summaryBaseline == "" {
		return &sarif.TriageView{Suppressions: sarif.CollectSuppressionStats(report)}
	}

	baseline, absBaselinePath := loadBaselineOrExit(summaryBaseline, absSarifPath)
	outcome, err := triage.Apply(report, triage.Options{
		Baseline:       baseline,
		BaselinePath:   absBaselinePath,
		FingerprintKey: summaryFingerprintKey,
		ReadOnly:       true,
	})
	if err != nil {
		out.Fatalf("%s", err)
	}
	return outcome.View
}

var showFindings bool
var showCodeSnippets bool
var verboseFlow bool

var summaryPaths []string
var summarySeverities []string
var summaryRuleIDs []string
var summaryFingerprints []string
var summaryPartialFingerprintKey string
var summaryGroupBy string
var summaryMaxNestingLevel = -1 // -1 = no cap; >= 0 collapses deeper flow steps
var summaryCodeFlow string
var summaryBaseline string
var summaryBaselineStates []string
var summaryFingerprintKey string
var summaryShowSuppressed bool

func init() {
	rootCmd.AddCommand(summaryCmd)

	summaryCmd.Flags().BoolVar(&showFindings, "show-findings", false, "Show every finding in the SARIF report")
	summaryCmd.Flags().BoolVar(&showCodeSnippets, "show-code-snippets", false, "Show finding related code snippets")
	summaryCmd.Flags().BoolVar(&verboseFlow, "verbose-flow", false, "Show full code flow steps for findings")
	summaryCmd.Flags().StringArrayVar(&summaryPaths, "path", nil, "Show only findings whose file path matches this glob (** supported, repeatable)")
	summaryCmd.Flags().StringArrayVar(&summarySeverities, "severity", nil, "Show only findings at these SARIF levels: note, warning, error, none (repeatable)")
	summaryCmd.Flags().StringArrayVar(&summaryRuleIDs, "rule-id", nil, "Show only findings from this rule: full id, leaf name, or glob (repeatable)")
	summaryCmd.Flags().StringArrayVar(&summaryFingerprints, "partial-fingerprint", nil, "Show only findings whose partial fingerprint starts with this value (git-hash style, repeatable)")
	summaryCmd.Flags().StringVar(&summaryPartialFingerprintKey, "partial-fingerprint-key", "", "partialFingerprints key matched by --partial-fingerprint (defaults to vulnerabilityWithTraceHash/v1)")
	summaryCmd.Flags().IntVar(&summaryMaxNestingLevel, "max-nesting-level", -1, "Collapse code-flow steps deeper than this call-nesting level (-1 = no cap)")
	summaryCmd.Flags().StringVar(&summaryGroupBy, "group-by", "", "Group the --show-findings listing by: severity, rule-id, file-path (defaults to file-path)")
	summaryCmd.Flags().StringVar(&summaryCodeFlow, "code-flow", "", "Render code flows: \"all\", a 1-based index, or unset (first only)")
	addBaselineFlags(summaryCmd, &summaryBaseline, &summaryFingerprintKey)
	summaryCmd.Flags().StringArrayVar(&summaryBaselineStates, "baseline-state", nil, "Show only findings in this baseline state: new, unchanged, updated, absent (repeatable, needs --baseline)")
	summaryCmd.Flags().BoolVar(&summaryShowSuppressed, "suppressed", false, "Include suppressed findings in the listing")
}

// addBaselineFlags registers the flags shared by every command that can compare
// a report against a baseline.
func addBaselineFlags(cmd *cobra.Command, baseline *string, fingerprintKey *string) {
	cmd.Flags().StringVar(baseline, "baseline", "", "Previous SARIF report to compare against and inherit suppressions from")
	cmd.Flags().StringVar(fingerprintKey, "fingerprint-key", "", "partialFingerprints key identifying a finding across reports (default "+sarif.DefaultIdentityKey+")")
}

// loadBaselineOrExit resolves and loads a baseline report, refusing to use the
// report under inspection as its own baseline.
func loadBaselineOrExit(baselinePath, absReportPath string) (*sarif.Report, string) {
	absBaselinePath := log.AbsPathOrExit(baselinePath, "baseline")
	if absBaselinePath == absReportPath {
		out.Fatalf("The baseline and the report are the same file: %s", absBaselinePath)
	}
	baseline, err := sarif.LoadReport(absBaselinePath)
	if err != nil {
		out.Fatalf("Failed to load baseline report: %s", err)
	}
	return baseline, absBaselinePath
}

// currentSummaryBuilder returns a builder pre-populated with the user's current summary flags.
// All summary command suggestions should use this as the base to ensure that adding a new
// flag in one place automatically propagates to every suggestion.
func currentSummaryBuilder(sarifPath string) *utils.OpentaintCommandBuilder {
	builder := utils.NewSummaryCommand(sarifPath)
	if showFindings {
		builder.WithShowFindings()
	}
	if showCodeSnippets {
		builder.WithShowCodeSnippets()
	}
	if verboseFlow {
		builder.WithVerboseFlow()
	}
	builder.WithPath(summaryPaths)
	builder.WithSeverity(summarySeverities)
	builder.WithRuleID(summaryRuleIDs)
	builder.WithPartialFingerprint(summaryFingerprints)
	builder.WithPartialFingerprintKey(summaryPartialFingerprintKey)
	builder.WithMaxNestingLevel(summaryMaxNestingLevel)
	builder.WithGroupBy(summaryGroupBy)
	builder.WithCodeFlow(summaryCodeFlow)
	builder.WithBaseline(summaryBaseline)
	builder.WithFingerprintKey(summaryFingerprintKey)
	builder.WithBaselineStateFilter(summaryBaselineStates)
	builder.WithSuppressed(summaryShowSuppressed)
	return builder
}

// summaryFilters builds the sarif filter set from the user's summary flag globals.
// Returns the zero Filters value (no filtering) when called from scan, where the
// flag globals are at their defaults.
func summaryFilters() sarif.Filters {
	return sarif.Filters{
		Paths:          summaryPaths,
		Severities:     summarySeverities,
		RuleIDs:        summaryRuleIDs,
		Fingerprints:   summaryFingerprints,
		FingerprintKey: summaryPartialFingerprintKey,
	}
}

// summaryListingOptions builds the listing options from the user's flag globals
// plus the pre-parsed group dimension and code-flow selection. Keeping the
// parses at the Run call site means we validate-once and never silently re-parse
// downstream.
func summaryListingOptions(dim sarif.GroupDimension, codeFlowSel sarif.CodeFlowSelection) sarif.ListingOptions {
	return sarif.ListingOptions{
		ShowCodeSnippets: showCodeSnippets,
		VerboseFlow:      verboseFlow,
		MaxNestingLevel:  summaryMaxNestingLevel,
		GroupBy:          dim,
		FingerprintKey:   summaryPartialFingerprintKey,
		CodeFlows:        codeFlowSel,
		ShowSuppressed:   summaryShowSuppressed,
	}
}

// printSarifSummary renders the optional finding listing followed by the scan
// summary. list controls whether the listing is printed; each command owns its
// own --show-findings flag.
func printSarifSummary(report *sarif.Report, absSarifPath string, filters sarif.Filters, opts sarif.ListingOptions, view *sarif.TriageView, list bool) {
	filtered := report.Filter(filters)

	hasOmittedFlow := false
	if list {
		hasOmittedFlow = filtered.PrintAll(out, opts)
		out.Blank()
	}

	filtered.PrintSummary(out, absSarifPath, view)

	if list && hasOmittedFlow && !verboseFlow {
		out.Suggest(
			"To see the full code flow and code snippets, run:",
			currentSummaryBuilder(absSarifPath).WithVerboseFlow().WithShowCodeSnippets().Build(),
		)
	}
}
