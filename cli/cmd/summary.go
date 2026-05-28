package cmd

import (
	"github.com/seqra/opentaint/internal/sarif"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

// summaryCmd represents the summary command
var summaryCmd = &cobra.Command{
	Use:   "summary sarif",
	Short: "Print summary of your sarif",
	Args:  cobra.ExactArgs(1), // require exactly one argument
	Long: `Print summary of your sarif file

Arguments:
  sarif  - Path to a sarif file
`,

	Run: func(cmd *cobra.Command, args []string) {
		for _, s := range summarySeverities {
			if err := sarif.ValidateSeverity(s); err != nil {
				out.Fatalf("%s", err)
			}
		}
		if _, err := sarif.ParseGroupDimension(summaryGroupBy); err != nil {
			out.Fatalf("%s", err)
		}
		if _, err := sarif.ParseCodeFlowSelection(summaryCodeFlow); err != nil {
			out.Fatalf("%s", err)
		}

		absSarifPath := log.AbsPathOrExit(args[0], "sarif path")
		report, err := sarif.LoadReport(absSarifPath)
		if err != nil {
			out.Fatalf("Failed to load SARIF report: %s", err)
		}
		printSarifSummary(report, absSarifPath)
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

	summaryCmd.Flags().BoolVar(&showFindings, "show-findings", false, "Show all issues from Sarif file")
	summaryCmd.Flags().BoolVar(&showCodeSnippets, "show-code-snippets", false, "Show finding related code snippets")
	summaryCmd.Flags().BoolVar(&verboseFlow, "verbose-flow", false, "Show full code flow steps for findings")
	summaryCmd.Flags().StringArrayVar(&summaryPaths, "path", nil, "Show only findings whose file path matches this glob (** supported, repeatable)")
	summaryCmd.Flags().StringArrayVar(&summarySeverities, "severity", nil, "Show only findings of this SARIF level: error, warning, note, none (repeatable)")
	summaryCmd.Flags().StringArrayVar(&summaryRuleIDs, "rule-id", nil, "Show only findings for this rule: full id, leaf name, or glob (repeatable)")
	summaryCmd.Flags().StringArrayVar(&summaryFingerprints, "partial-fingerprint", nil, "Show only findings whose partial fingerprint starts with this value (git-hash style, repeatable)")
	summaryCmd.Flags().StringVar(&summaryFingerprintKey, "partial-fingerprint-key", "", "partialFingerprints key matched by --partial-fingerprint (default vulnerabilityWithTraceHash/v1)")
	summaryCmd.Flags().IntVar(&summaryMaxNestingLevel, "max-nesting-level", -1, "Collapse code-flow steps deeper than this call-nesting level (-1 = no cap)")
	summaryCmd.Flags().StringVar(&summaryGroupBy, "group-by", "", "Group the --show-findings listing by: severity, rule-id, file-path (default file-path)")
	summaryCmd.Flags().StringVar(&summaryCodeFlow, "code-flow", "", "Render code flows: \"all\", a 1-based index, or unset (first only)")
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
	builder.WithPartialFingerprintKey(summaryFingerprintKey)
	builder.WithMaxNestingLevel(summaryMaxNestingLevel)
	builder.WithGroupBy(summaryGroupBy)
	builder.WithCodeFlow(summaryCodeFlow)
	return builder
}

func printSarifSummary(report *sarif.Report, absSarifPath string) {
	filtered := report.Filter(sarif.Filters{
		Paths:          summaryPaths,
		Severities:     summarySeverities,
		RuleIDs:        summaryRuleIDs,
		Fingerprints:   summaryFingerprints,
		FingerprintKey: summaryFingerprintKey,
	})

	// summaryGroupBy is either "" (called from scan; ParseGroupDimension("") is valid
	// and yields the file-path default) or pre-validated in Run (called from summary),
	// so the error here cannot fire on either call path.
	dim, _ := sarif.ParseGroupDimension(summaryGroupBy)

	hasOmittedFlow := false
	if showFindings {
		// summaryCodeFlow is either "" (called from scan; ParseCodeFlowSelection("") is valid
		// and yields the first-flow default) or pre-validated in Run (called from summary),
		// so the error here cannot fire on either call path.
		codeFlowSel, _ := sarif.ParseCodeFlowSelection(summaryCodeFlow)
		opts := sarif.ListingOptions{
			ShowCodeSnippets: showCodeSnippets,
			VerboseFlow:      verboseFlow,
			MaxNestingLevel:  summaryMaxNestingLevel,
			GroupBy:          dim,
			FingerprintKey:   summaryFingerprintKey,
			CodeFlows:        codeFlowSel,
		}
		hasOmittedFlow = filtered.PrintAll(out, opts)
		out.Blank()
	}

	filtered.PrintSummary(out, absSarifPath)

	if showFindings && hasOmittedFlow && !verboseFlow {
		out.Suggest(
			"To see full code flow and code snippets, use:",
			currentSummaryBuilder(absSarifPath).WithVerboseFlow().WithShowCodeSnippets().Build(),
		)
	}
}
