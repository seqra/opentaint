// Package triage applies baselines and suppressions to a SARIF report. It is
// the single implementation behind the `triage` command, the annotation step of
// `scan`, and the read-only view `summary` renders.
package triage

import (
	"fmt"

	"github.com/seqra/opentaint/internal/sarif"
)

// Options describes one triage pass over a report.
type Options struct {
	// Baseline is the previously produced report to compare against, or nil.
	Baseline *sarif.Report
	// BaselinePath is that report's path, for display only.
	BaselinePath string
	// WriteBaselineState persists result.baselineState and run.baselineGuid.
	// Without it the comparison only drives what is printed.
	WriteBaselineState bool
	// FingerprintKey selects the identity fingerprint ("" = default).
	FingerprintKey string
	// ReadOnly means the caller will never persist the report. The comparison is
	// still applied to the in-memory copy so that --baseline-state can filter on
	// it, but nothing is reported as written or changed. This is what summary
	// uses.
	ReadOnly bool

	// Accept, Defer and Unsuppress name findings by fingerprint prefix.
	Accept     []string
	Defer      []string
	Unsuppress []string
	// Justification is required whenever Accept or Defer is non-empty.
	Justification string
}

// suppressing reports whether the options author any new decision.
func (o Options) suppressing() bool {
	return len(o.Accept) > 0 || len(o.Defer) > 0
}

// Outcome is what one triage pass produced.
type Outcome struct {
	// View is the baseline and suppression state to print.
	View *sarif.TriageView
	// Changed reports whether the report was modified and needs writing back.
	Changed bool
}

// Apply runs a triage pass over report, mutating it in place.
//
// Order matters: suppressions are inherited from the baseline first, so that a
// decision made in a previous cycle is visible; then explicit accept/defer
// decisions from this run overwrite them; then the baseline comparison is
// computed over the final state.
func Apply(report *sarif.Report, opts Options) (*Outcome, error) {
	key, err := sarif.ResolveIdentityKey(opts.FingerprintKey)
	if err != nil {
		return nil, err
	}
	if opts.suppressing() && opts.Justification == "" {
		return nil, fmt.Errorf("a justification is required to suppress a finding: pass --justification")
	}

	view := &sarif.TriageView{BaselinePath: opts.BaselinePath, ReadOnly: opts.ReadOnly}
	changed := false

	if opts.Baseline != nil {
		view.Inherited = sarif.InheritSuppressions(report, opts.Baseline, key)
		changed = changed || view.Inherited > 0
	}

	added, err := applyDecisions(report, key, opts)
	if err != nil {
		return nil, err
	}
	view.Added = added
	changed = changed || added > 0

	removed, err := applyUnsuppressions(report, key, opts.Unsuppress)
	if err != nil {
		return nil, err
	}
	changed = changed || removed > 0

	if opts.Baseline != nil {
		comparison, err := sarif.CompareToBaseline(report, opts.Baseline, key)
		if err != nil {
			return nil, err
		}
		view.Comparison = comparison
		if opts.WriteBaselineState || opts.ReadOnly {
			comparison.Apply(report)
			view.StateWritten = opts.WriteBaselineState && !opts.ReadOnly
			changed = changed || view.StateWritten
		}
	}

	if opts.ReadOnly {
		changed = false
	}
	if changed {
		// A report the CLI has written must be citable as the next baseline.
		sarif.EnsureRunGUIDs(report)
	}

	view.Suppressions = sarif.CollectSuppressionStats(report)
	return &Outcome{View: view, Changed: changed}, nil
}

// applyDecisions resolves each accept/defer prefix and records the decision.
// Every prefix is resolved before anything is written, so a typo in the second
// of three prefixes leaves the report untouched rather than half-triaged.
func applyDecisions(report *sarif.Report, key string, opts Options) (int, error) {
	type decision struct {
		result *sarif.Result
		accept bool
	}

	var decisions []decision
	for _, prefix := range opts.Accept {
		r, err := sarif.ResolvePrefix(report, key, prefix)
		if err != nil {
			return 0, err
		}
		decisions = append(decisions, decision{result: r, accept: true})
	}
	for _, prefix := range opts.Defer {
		r, err := sarif.ResolvePrefix(report, key, prefix)
		if err != nil {
			return 0, err
		}
		decisions = append(decisions, decision{result: r})
	}

	for _, d := range decisions {
		var err error
		if d.accept {
			err = sarif.Accept(d.result, opts.Justification)
		} else {
			err = sarif.Defer(d.result, opts.Justification)
		}
		if err != nil {
			return 0, err
		}
	}
	return len(decisions), nil
}

// applyUnsuppressions resolves every prefix before removing anything, for the
// same all-or-nothing reason as applyDecisions.
func applyUnsuppressions(report *sarif.Report, key string, prefixes []string) (int, error) {
	var targets []*sarif.Result
	for _, prefix := range prefixes {
		r, err := sarif.ResolvePrefix(report, key, prefix)
		if err != nil {
			return 0, err
		}
		targets = append(targets, r)
	}

	removed := 0
	for _, r := range targets {
		if sarif.Unsuppress(r) {
			removed++
		}
	}
	return removed, nil
}
