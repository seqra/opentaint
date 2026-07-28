package cmd

import (
	"fmt"
	"os"

	"github.com/seqra/opentaint/internal/sarif"
	"github.com/seqra/opentaint/internal/triage"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

// ExitFindings is returned when --error-on-findings is set and findings remain.
// It matches the "results failed the check" code used by `opentaint test`, and
// stays clear of 1 (general failure) and 252-255 (analyzer failures).
const ExitFindings = 2

type TriageConfig struct {
	Baseline           string
	WriteBaselineState bool
	FingerprintKey     string
	Accept             []string
	Defer              []string
	Unsuppress         []string
	Justification      string
	Output             string
	ErrorOnFindings    bool
	ErrorOnSeverity    []string
	ShowSuppressed     bool
	ShowFindings       bool
}

var triageFlags TriageConfig

var triageCmd = &cobra.Command{
	Use:   "triage sarif",
	Short: "Compare a SARIF report against a baseline and record suppressions",
	Args:  cobra.ExactArgs(1),
	Long: `Compare a SARIF report against a baseline and record accept/defer decisions

Findings are identified by fingerprint, so a decision survives edits elsewhere
in the code. Nothing is ever deleted from the report: an accepted or deferred
finding stays in the file, marked with a SARIF suppression that records who
decided what and why.

Arguments:
  sarif  - Path to the SARIF report to triage

A finding is named by a fingerprint prefix, git-style — the value shown as
"Fingerprint:" by 'opentaint summary --show-findings'.

Examples:
  # See what changed since the last release, without modifying anything
  opentaint triage scan.sarif --baseline release.sarif

  # We will not fix this one
  opentaint triage scan.sarif --accept q3Vf9k --justification "sink is a constant"

  # We are not fixing this one for now
  opentaint triage scan.sarif --defer 8bc1d2 --justification "waiting on OT-412"

  # Carry earlier decisions forward and fail if anything new turned up
  opentaint triage scan.sarif --baseline release.sarif -o triaged.sarif \
      --error-on-findings

Exit codes:
  0    Triage completed
  1    General failure (bad input, unreadable report)
  2    Findings remain and --error-on-findings was set`,

	Run: func(cmd *cobra.Command, args []string) {
		runTriage(triageFlags, args[0])
	},
}

func init() {
	rootCmd.AddCommand(triageCmd)

	addBaselineFlags(triageCmd, &triageFlags.Baseline, &triageFlags.FingerprintKey)
	triageCmd.Flags().BoolVar(&triageFlags.WriteBaselineState, "write-baseline-state", false, "Persist result.baselineState and run.baselineGuid into the output report (needs --baseline)")
	triageCmd.Flags().StringArrayVar(&triageFlags.Accept, "accept", nil, "Accept the finding with this fingerprint prefix: won't fix (repeatable)")
	triageCmd.Flags().StringArrayVar(&triageFlags.Defer, "defer", nil, "Defer the finding with this fingerprint prefix: not fixing for now (repeatable)")
	triageCmd.Flags().StringArrayVar(&triageFlags.Unsuppress, "unsuppress", nil, "Remove the suppression from the finding with this fingerprint prefix (repeatable)")
	triageCmd.Flags().StringVar(&triageFlags.Justification, "justification", "", "Why the finding is accepted or deferred (required with --accept/--defer)")
	triageCmd.Flags().StringVarP(&triageFlags.Output, "output", "o", "", "Write the triaged report here (default: rewrite the input in place)")
	addGateFlags(triageCmd, &triageFlags.ErrorOnFindings, &triageFlags.ErrorOnSeverity)
	triageCmd.Flags().BoolVar(&triageFlags.ShowSuppressed, "suppressed", false, "Include suppressed findings in the listing")
	triageCmd.Flags().BoolVar(&triageFlags.ShowFindings, "show-findings", false, "List the findings, not just the summary")
}

// addGateFlags registers the failure-gate flags shared by scan and triage.
func addGateFlags(cmd *cobra.Command, errorOnFindings *bool, severities *[]string) {
	cmd.Flags().BoolVar(errorOnFindings, "error-on-findings", false, "Exit with code 2 when findings remain (new ones only, with --baseline)")
	cmd.Flags().StringArrayVar(severities, "error-on-severity", nil, "Restrict --error-on-findings to these levels: error, warning, note, none (comma-separated or repeated; default all)")
}

func runTriage(cfg TriageConfig, reportPath string) {
	gateSeverities, err := triage.ParseGateSeverities(cfg.ErrorOnSeverity)
	if err != nil {
		out.Fatalf("%s", err)
	}

	absReportPath := log.AbsPathOrExit(reportPath, "sarif path")
	report, err := sarif.LoadReport(absReportPath)
	if err != nil {
		out.Fatalf("Failed to load SARIF report: %s", err)
	}

	opts := triage.Options{
		WriteBaselineState: cfg.WriteBaselineState,
		FingerprintKey:     cfg.FingerprintKey,
		Accept:             cfg.Accept,
		Defer:              cfg.Defer,
		Unsuppress:         cfg.Unsuppress,
		Justification:      cfg.Justification,
	}
	if cfg.Baseline != "" {
		opts.Baseline, opts.BaselinePath = loadBaselineOrExit(cfg.Baseline, absReportPath)
	} else if cfg.WriteBaselineState {
		out.Fatalf("--write-baseline-state needs a --baseline to compare against")
	}

	outcome, err := triage.Apply(report, opts)
	if err != nil {
		out.Fatalf("%s", err)
	}

	outputPath := absReportPath
	if cfg.Output != "" {
		outputPath = log.AbsPathOrExit(cfg.Output, "output")
	}
	// Writing an unchanged report to its own path would be pure churn, but an
	// explicit -o means "put a copy here" and is always honored.
	if outcome.Changed || outputPath != absReportPath {
		if err := sarif.SaveReport(report, outputPath); err != nil {
			out.Fatalf("Failed to write report: %s", err)
		}
	}

	printSarifSummary(report, outputPath, sarif.Filters{}, sarif.ListingOptions{
		MaxNestingLevel: -1,
		ShowSuppressed:  cfg.ShowSuppressed,
	}, outcome.View, cfg.ShowFindings)

	exitOnGate(triage.Gate{Enabled: cfg.ErrorOnFindings, Severities: gateSeverities}, report, outcome.View)
}

// exitOnGate reports the gate verdict and exits with ExitFindings when it trips.
func exitOnGate(gate triage.Gate, report *sarif.Report, view *sarif.TriageView) {
	count, tripped := gate.Evaluate(report, view)
	if !tripped {
		return
	}
	out.Blank()
	scope := "finding"
	if count != 1 {
		scope = "findings"
	}
	qualifier := ""
	if view != nil && view.Comparison != nil {
		qualifier = "new "
	}
	out.Error(fmt.Sprintf("%d %s%s reported (--error-on-findings)", count, qualifier, scope))
	os.Exit(ExitFindings)
}
