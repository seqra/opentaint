package cmd

import (
	"github.com/seqra/opentaint/internal/sarif"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

// summaryCmd represents the summary command
var summaryCmd = &cobra.Command{
	Use:   "summary <sarif-report>",
	Short: "Show a summary of a SARIF report",
	Long:  "Show a summary of a SARIF report.\n\nArguments:\n  <sarif-report>  SARIF report from `opentaint scan` or a test run",
	Example: `  # Show the summary of a report
  opentaint summary .opentaint/results/report.sarif

  # List the errors in the main sources
  opentaint summary .opentaint/results/report.sarif --show-findings \
    --severity error --path "src/main/**"

  # Show the path traversal findings with full code flows and code
  opentaint summary .opentaint/results/report.sarif --show-findings \
    --rule-id path-traversal --verbose-flow --show-code-snippets`,
	Args: cobra.ExactArgs(1), // require exactly one argument
	Run: func(cmd *cobra.Command, args []string) {
		for _, s := range summarySeverities {
			if err := sarif.ValidateSeverity(s); err != nil {
				out.FatalErr(err)
			}
		}
		dim, err := sarif.ParseGroupDimension(summaryGroupBy)
		if err != nil {
			out.FatalErr(err)
		}
		codeFlowSel, err := sarif.ParseCodeFlowSelection(summaryCodeFlow)
		if err != nil {
			out.FatalErr(err)
		}

		absSarifPath := log.AbsPathOrExit(args[0], "sarif path")
		report, err := sarif.LoadReport(absSarifPath)
		if err != nil {
			out.Fatal("Failed to load the SARIF report", err)
		}
		filters := summaryFilters()
		matched := sarif.GenerateSummary(report.Filter(filters)).TotalFindings
		if filters.Active() && matched == 0 {
			out.Print("No findings match the filters")
			return
		}
		hasOmittedFlow := printSarifSummary(report, absSarifPath, filters, summaryListingOptions(dim, codeFlowSel))

		if showFindings && hasOmittedFlow && !verboseFlow {
			out.Suggest(
				"To see the full code flow and code snippets, run:",
				currentSummaryBuilder(args[0]).WithVerboseFlow().WithShowCodeSnippets().Build(),
			)
		}
		if !showFindings && matched > 0 {
			out.Suggest(
				"To list the findings, run:",
				currentSummaryBuilder(args[0]).WithShowFindings().Build(),
			)
		}
	},
}

var showFindings bool
var showCodeSnippets bool
var verboseFlow bool

var summaryPaths []string
var summarySeverities []string
var summaryRuleIDs []string
var summaryFingerprints []string
var summaryFingerprintKey string
var summaryGroupBy string
var summaryMaxNestingLevel = -1 // -1 = no cap; >= 0 collapses deeper flow steps
var summaryCodeFlow string

func init() {
	rootCmd.AddCommand(summaryCmd)

	summaryCmd.Flags().BoolVar(&showFindings, "show-findings", false, "List the findings")
	summaryCmd.Flags().BoolVar(&showCodeSnippets, "show-code-snippets", false, "Show the code snippet of each finding")
	summaryCmd.Flags().BoolVar(&verboseFlow, "verbose-flow", false, "Show every code-flow step, not only the source and sink")
	summaryCmd.Flags().StringArrayVar(&summaryPaths, "path", nil, "Show only findings whose file path matches this glob (e.g. src/main/**) (repeatable)")
	summaryCmd.Flags().StringArrayVar(&summarySeverities, "severity", nil, "Show only findings of this SARIF level: note, warning, error, or none (repeatable)")
	summaryCmd.Flags().StringArrayVar(&summaryRuleIDs, "rule-id", nil, "Show only findings of this rule: full ID, leaf name, or glob (repeatable)")
	summaryCmd.Flags().StringArrayVar(&summaryFingerprints, "partial-fingerprint", nil, "Show only findings whose partial fingerprint starts with this prefix (repeatable)")
	summaryCmd.Flags().StringVar(&summaryFingerprintKey, "partial-fingerprint-key", sarif.DefaultFingerprintKey, "SARIF partialFingerprints key that --partial-fingerprint matches")
	summaryCmd.Flags().IntVar(&summaryMaxNestingLevel, "max-nesting-level", -1, "Hide code-flow steps deeper than this call-nesting level (-1 = off)")
	summaryCmd.Flags().StringVar(&summaryGroupBy, "group-by", "file-path", "Group findings by severity, rule-id, or file-path")
	summaryCmd.Flags().StringVar(&summaryCodeFlow, "code-flow", "", "Code flows to show for each finding: all or a 1-based index (default: the first)")
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
	if summaryFingerprintKey != sarif.DefaultFingerprintKey {
		builder.WithPartialFingerprintKey(summaryFingerprintKey)
	}
	builder.WithMaxNestingLevel(summaryMaxNestingLevel)
	builder.WithGroupBy(summaryGroupBy)
	builder.WithCodeFlow(summaryCodeFlow)
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
		FingerprintKey: summaryFingerprintKey,
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
		FingerprintKey:   summaryFingerprintKey,
		CodeFlows:        codeFlowSel,
	}
}

// printSarifSummary prints the findings when --show-findings is set and the summary block. It
// reports whether the listing omitted a part of some code flow.
func printSarifSummary(report *sarif.Report, absSarifPath string, filters sarif.Filters, opts sarif.ListingOptions, extraOutputs ...any) bool {
	filtered := report.Filter(filters)

	hasOmittedFlow := false
	if showFindings {
		hasOmittedFlow = filtered.PrintAll(out, opts)
		out.Blank()
	}

	filtered.PrintSummary(out, absSarifPath, extraOutputs...)
	return hasOmittedFlow
}
