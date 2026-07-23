package sarif

import (
	"fmt"

	"github.com/seqra/opentaint/internal/output"
)

// TriageView is the baseline and suppression state of a report, as computed by
// the command that is about to print it. A nil *TriageView means neither
// applies and the summary renders exactly as it did before triage existed.
type TriageView struct {
	// BaselinePath is the baseline the report was compared against, shown so the
	// reader can tell which report the counts are relative to.
	BaselinePath string
	// Comparison is the classification against that baseline, or nil when no
	// baseline was supplied.
	Comparison *Comparison
	// StateWritten records whether baselineState was persisted into the report
	// (--baseline-state) or only computed for display.
	StateWritten bool
	// ReadOnly means the command never writes the report, so reporting whether
	// the state was persisted would be noise.
	ReadOnly bool

	// Suppressions counts the suppression state of the report.
	Suppressions SuppressionStats
	// Inherited counts suppressions carried over from the baseline in this run.
	Inherited int
	// Added counts suppressions authored in this run (triage --accept/--defer).
	Added int
}

// baselineItems renders the Baseline group, or nil when no baseline applies.
// Zero-valued state counts are omitted so the group stays readable; the states
// that matter are the ones that happened.
func (v *TriageView) baselineItems(out *output.Printer) []any {
	if v == nil || v.Comparison == nil {
		return nil
	}

	items := []any{}
	if v.BaselinePath != "" {
		items = append(items, out.FieldItem("Baseline", v.BaselinePath))
	}
	for _, entry := range []struct {
		label string
		state BaselineState
	}{
		{"New", New},
		{"Unchanged", Unchanged},
		{"Updated", Updated},
	} {
		if count := v.Comparison.Counts[entry.state]; count > 0 {
			items = append(items, out.FieldItem(entry.label, count))
		}
	}
	// "Fixed" reads better than SARIF's "absent" for a finding that is gone.
	if count := v.Comparison.Counts[Absent]; count > 0 {
		items = append(items, out.FieldItem("Fixed", count))
	}
	if v.Comparison.Unmatchable > 0 {
		items = append(items, out.FieldItem("Not comparable", v.Comparison.Unmatchable))
	}

	if v.ReadOnly {
		return items
	}
	written := "no"
	if v.StateWritten {
		written = "yes"
	}
	return append(items, out.FieldItem("Written to report", written))
}

// suppressionItems renders the Suppressions group, or nil when the report
// carries no suppressions at all.
func (v *TriageView) suppressionItems(out *output.Printer) []any {
	if v == nil || !v.Suppressions.Any() {
		return nil
	}

	stats := v.Suppressions
	items := []any{
		out.FieldItem("Suppressed", suppressedOf(stats)),
	}
	if stats.WontFix > 0 {
		items = append(items, out.FieldItem("Won't fix", stats.WontFix))
	}
	if stats.Deferred > 0 {
		items = append(items, out.FieldItem("Deferred", stats.Deferred))
	}
	if stats.NotHonored > 0 {
		items = append(items, out.FieldItem("Not honored", stats.NotHonored))
	}
	if v.Inherited > 0 {
		items = append(items, out.FieldItem("Inherited from baseline", v.Inherited))
	}
	if v.Added > 0 {
		items = append(items, out.FieldItem("Added this run", v.Added))
	}
	return items
}

func suppressedOf(stats SuppressionStats) string {
	return fmt.Sprintf("%d of %d", stats.Suppressed, stats.Total)
}
