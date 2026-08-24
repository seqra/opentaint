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
	Justifications     []string
	Output             string
	ErrorOnFindings    bool
	ErrorOnSeverity    []string
	ShowSuppressed     bool
	ShowFindings       bool
}

var triageFlags TriageConfig

var triageCmd = &cobra.Command{
	Use:   "triage <sarif-report>",
	Short: "Compare a report against a baseline and record suppressions",
	Args:  cobra.ExactArgs(1),
	Long: `Compare a SARIF report with a baseline and record triage decisions. To accept a finding means: the team will not fix it. To defer a finding means: the team will not fix it now. Both decisions become SARIF suppressions. All SARIF tools obey them.

The sarif-report argument is the path to the report to triage. It is required. Use a report from "opentaint scan". A fingerprint identifies each finding. Thus a decision stays attached when other code changes. The command deletes nothing. An accepted or deferred finding stays in the report. A suppression marks it and keeps the decision and its justification.

To name a finding, give a prefix of its fingerprint, as with a git hash. Use the value that "opentaint summary --show-findings" shows as "Fingerprint:". The two commands read the same key. Thus the value on the screen is the value to paste. The --fingerprint-key flag changes the key for both commands. A prefix that is unknown, or that matches two different values, causes an error. The command does not guess.

The command writes the triaged report in place. To write it to a different path, use --output. With --baseline, findings first get the decisions that the baseline recorded for them. Thus a sequence of reports keeps its triage history.

Use "opentaint scan" to make the report that this command triages. To read the result, use "opentaint summary".

Exit codes:
  0    Triage completed
  1    General failure (bad input, unreadable report)
  2    Findings remain and --error-on-findings was set`,
	Example: `  # See what changed since the last release, without a change to the files
  opentaint triage report.sarif --baseline release.sarif

  # Record that a finding will not be fixed
  opentaint triage report.sarif --accept q3Vf9k --justification "sink is a constant"

  # Record that a finding will not be fixed now
  opentaint triage report.sarif --defer 8bc1d2 --justification "waiting on OT-412"

  # Remove an earlier decision
  opentaint triage report.sarif --unsuppress q3Vf9k

  # Keep earlier decisions and fail if a new finding appeared
  opentaint triage report.sarif --baseline release.sarif -o triaged.sarif --error-on-findings

  # Recipe: triage a fresh report, one decision at a time
  opentaint summary report.sarif --show-findings
  opentaint triage report.sarif --accept <fingerprint> --justification "why it is safe"
  opentaint triage report.sarif --defer <fingerprint> --justification "why it can wait"
  opentaint summary report.sarif --suppressed

  # Recipe: roll the baseline forward after a release
  opentaint triage report.sarif --baseline baselines/main.sarif -o triaged.sarif
  cp triaged.sarif baselines/main.sarif`,

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
	triageCmd.Flags().StringArrayVar(&triageFlags.Justifications, "justification", nil, "Why the finding is accepted or deferred (required with --accept/--defer, one per run)")
	triageCmd.Flags().StringVarP(&triageFlags.Output, "output", "o", "", "Path to write the triaged report (defaults to rewriting the input in place)")
	addGateFlags(triageCmd, &triageFlags.ErrorOnFindings, &triageFlags.ErrorOnSeverity)
	triageCmd.Flags().BoolVar(&triageFlags.ShowSuppressed, "suppressed", false, "Include suppressed findings in the listing")
	triageCmd.Flags().BoolVar(&triageFlags.ShowFindings, "show-findings", false, "Show every finding, not just the summary")
}

// addGateFlags registers the failure-gate flags shared by scan and triage.
func addGateFlags(cmd *cobra.Command, errorOnFindings *bool, severities *[]string) {
	cmd.Flags().BoolVar(errorOnFindings, "error-on-findings", false, "Exit with code 2 when findings remain (with --baseline, only new ones count)")
	cmd.Flags().StringArrayVar(severities, "error-on-severity", nil, "Restrict --error-on-findings to these levels: note, warning, error, none (repeatable or comma-separated, defaults to all)")
}

func runTriage(cfg TriageConfig, reportPath string) {
	gateSeverities, err := triage.ParseGateSeverities(cfg.ErrorOnSeverity)
	if err != nil {
		out.Fatalf("%s", err)
	}
	justification, err := singleJustification(cfg.Justifications)
	if err != nil {
		out.Fatalf("%s", err)
	}

	absReportPath := log.AbsPathOrExit(reportPath, "sarif path")
	report, err := sarif.LoadReport(absReportPath)
	if err != nil {
		out.Fatalf("Failed to load SARIF report: %s", err)
	}

	// The aliases (sink, source-sink, trace) are expanded once here, so the
	// listing shows fingerprints under the same full key the decisions resolve.
	identityKey, err := sarif.ResolveIdentityKey(cfg.FingerprintKey)
	if err != nil {
		out.Fatalf("%s", err)
	}

	opts := triage.Options{
		WriteBaselineState: cfg.WriteBaselineState,
		FingerprintKey:     identityKey,
		Accept:             cfg.Accept,
		Defer:              cfg.Defer,
		Unsuppress:         cfg.Unsuppress,
		Justification:      justification,
	}
	if cfg.Baseline != "" {
		opts.Baseline, opts.BaselinePath = loadBaselineOrExit(cfg.Baseline, absReportPath)
	} else if cfg.WriteBaselineState {
		out.Fatalf("--write-baseline-state needs a --baseline to compare against")
	}

	outputPath := absReportPath
	if cfg.Output != "" {
		outputPath = log.AbsPathOrExit(cfg.Output, "output")
	}
	// Overwriting the baseline would destroy the history the comparison and
	// the inherited suppressions are anchored to. The input side of the same
	// mistake is rejected in loadBaselineOrExit.
	if cfg.Baseline != "" && outputPath == opts.BaselinePath {
		out.Fatalf("--output would overwrite the baseline: %s\n"+
			"Write the triaged report to another path", outputPath)
	}

	outcome, err := triage.Apply(report, opts)
	if err != nil {
		out.Fatalf("%s", err)
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
		FingerprintKey:  identityKey,
	}, outcome.View, cfg.ShowFindings)

	exitOnGate(triage.Gate{Enabled: cfg.ErrorOnFindings, Severities: gateSeverities}, report, outcome.View)
}

// singleJustification enforces that one triage run records one reason. The flag
// is repeatable only so that passing it twice can be caught: a second
// --justification would otherwise overwrite the first, silently filing every
// decision in the run under the wrong reason.
func singleJustification(values []string) (string, error) {
	switch len(values) {
	case 0:
		return "", nil
	case 1:
		return values[0], nil
	default:
		return "", fmt.Errorf("--justification was given %d times, but one run records one reason.\n"+
			"Run triage once per justification, or pass a single --justification covering every finding in this run",
			len(values))
	}
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
