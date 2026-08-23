package sarif

import (
	"bytes"
	"strings"
	"testing"

	"github.com/seqra/opentaint/internal/output"
)

func renderSummary(t *testing.T, report *Report, view *TriageView) string {
	t.Helper()
	var buf bytes.Buffer
	report.PrintSummary(output.NewWithWriter(&buf), "/tmp/report.sarif", view)
	return buf.String()
}

func TestSummaryWithoutTriageHasNoNewGroups(t *testing.T) {
	out := renderSummary(t, makeReport(makeResult("a", Error, "a.java", 1, nil)), nil)
	if strings.Contains(out, "Baseline") {
		t.Errorf("unexpected Baseline group:\n%s", out)
	}
	if strings.Contains(out, "Suppressions") {
		t.Errorf("unexpected Suppressions group:\n%s", out)
	}
	if strings.Contains(out, "Reported") {
		t.Errorf("Reported line should only appear when something is suppressed:\n%s", out)
	}
}

func TestSummaryBaselineGroup(t *testing.T) {
	baseline := makeReport(
		makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")),
		makeResult("gone", Error, "c.java", 3, fp("id-gone", "trace-gone")),
	)
	report := makeReport(
		makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")),
		makeResult("fresh", Error, "b.java", 2, fp("id-fresh", "trace-fresh")),
	)
	cmp, err := CompareToBaseline(report, baseline, SourceSinkFingerprintKey)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}

	out := renderSummary(t, report, &TriageView{
		BaselinePath: "reports/main.sarif",
		Comparison:   cmp,
	})

	for _, want := range []string{"Baseline", "reports/main.sarif", "New", "Unchanged", "Fixed"} {
		if !strings.Contains(out, want) {
			t.Errorf("missing %q in summary:\n%s", want, out)
		}
	}
	if !strings.Contains(out, "Written to report") {
		t.Errorf("summary must say whether states were persisted:\n%s", out)
	}
}

func TestSummaryBaselineGroupOmitsZeroUpdated(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	report := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	cmp, _ := CompareToBaseline(report, baseline, SourceSinkFingerprintKey)

	out := renderSummary(t, report, &TriageView{BaselinePath: "b.sarif", Comparison: cmp})
	if strings.Contains(out, "Updated") {
		t.Errorf("zero-valued Updated line should be omitted:\n%s", out)
	}
	if !strings.Contains(out, "Unchanged") {
		t.Errorf("non-zero Unchanged should be shown:\n%s", out)
	}
}

func TestSummaryBaselineGroupReportsUnmatchable(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	report := makeReport(makeResult("nofp", Error, "b.java", 2, nil))
	cmp, _ := CompareToBaseline(report, baseline, SourceSinkFingerprintKey)

	out := renderSummary(t, report, &TriageView{BaselinePath: "b.sarif", Comparison: cmp})
	if !strings.Contains(out, "Not comparable") {
		t.Errorf("unmatchable findings must be surfaced:\n%s", out)
	}
}

func TestSummarySuppressionsGroup(t *testing.T) {
	report := makeReport(
		suppressed("a", "id-a", Accepted, "won't fix"),
		suppressed("b", "id-b", UnderReview, "not now"),
		makeResult("c", Error, "c.java", 3, fp("id-c", "trace-c")),
	)

	out := renderSummary(t, report, &TriageView{
		Suppressions: CollectSuppressionStats(report),
		Inherited:    1,
	})

	for _, want := range []string{"Suppressions", "Suppressed", "Won't fix", "Deferred", "Inherited from baseline"} {
		if !strings.Contains(out, want) {
			t.Errorf("missing %q in summary:\n%s", want, out)
		}
	}
	if !strings.Contains(out, "Reported") {
		t.Errorf("Findings group should report the unsuppressed count:\n%s", out)
	}
}

func TestSummarySuppressionsGroupShowsAddedOnlyWhenRelevant(t *testing.T) {
	report := makeReport(suppressed("a", "id-a", Accepted, "won't fix"))
	stats := CollectSuppressionStats(report)

	out := renderSummary(t, report, &TriageView{Suppressions: stats})
	if strings.Contains(out, "Added this run") {
		t.Errorf("Added line should be omitted when nothing was added:\n%s", out)
	}

	out = renderSummary(t, report, &TriageView{Suppressions: stats, Added: 1})
	if !strings.Contains(out, "Added this run") {
		t.Errorf("Added line expected:\n%s", out)
	}
}

func TestSummarySuppressionsGroupReportsNotHonored(t *testing.T) {
	report := makeReport(suppressed("a", "id-a", Rejected, "denied"))
	out := renderSummary(t, report, &TriageView{Suppressions: CollectSuppressionStats(report)})
	if !strings.Contains(out, "Not honored") {
		t.Errorf("rejected suppressions must be surfaced:\n%s", out)
	}
}

func TestRestrictCountsOnlyWhatTheFilterKept(t *testing.T) {
	baseline := makeReport(
		makeResult("sql", Error, "a.java", 1, fp("id-a", "trace-a")),
		makeResult("xss", Error, "b.java", 2, fp("id-b", "trace-b")),
		makeResult("sql", Error, "c.java", 3, fp("id-gone", "trace-gone")),
	)
	current := withRules(makeReport(
		makeResult("sql", Error, "a.java", 1, fp("id-a", "trace-a")),         // unchanged
		makeResult("xss", Error, "b.java", 2, fp("id-fresh", "trace-fresh")), // new
	), "sql", "xss")

	cmp, err := CompareToBaseline(current, baseline, SourceSinkFingerprintKey)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	cmp.Apply(current)
	view := &TriageView{Comparison: cmp, Suppressions: CollectSuppressionStats(current)}

	filters := Filters{RuleIDs: []string{"xss"}}
	restricted := view.Restrict(current.Filter(filters), filters)

	if got := restricted.Comparison.Counts[New]; got != 1 {
		t.Errorf("New = %d, want 1", got)
	}
	if got := restricted.Comparison.Counts[Unchanged]; got != 0 {
		t.Errorf("Unchanged = %d, want 0: the unchanged finding belongs to another rule", got)
	}
	// Two baseline findings are gone (id-b under xss, id-gone under sql). The
	// filter keeps only the xss one.
	if got := restricted.Comparison.Counts[Absent]; got != 1 {
		t.Errorf("Fixed = %d, want 1: only the xss finding survives the filter", got)
	}
	if got := view.Comparison.Counts[Absent]; got != 2 {
		t.Errorf("unrestricted Fixed = %d, want 2", got)
	}
	if got := restricted.Suppressions.Total; got != 1 {
		t.Errorf("Suppressions.Total = %d, want 1", got)
	}
	// The unrestricted view still describes the whole report.
	if got := view.Comparison.Counts[Unchanged]; got != 1 {
		t.Errorf("Restrict mutated the original view: Unchanged = %d, want 1", got)
	}
}

func TestRestrictKeepsFixedFindingsTheFilterNames(t *testing.T) {
	baseline := makeReport(makeResult("sql", Error, "c.java", 3, fp("id-gone", "trace-gone")))
	current := withRules(makeReport(), "sql")

	cmp, err := CompareToBaseline(current, baseline, SourceSinkFingerprintKey)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	view := &TriageView{Comparison: cmp}

	filters := Filters{BaselineStates: []string{"absent"}}
	restricted := view.Restrict(current.Filter(filters), filters)
	if got := restricted.Comparison.Counts[Absent]; got != 1 {
		t.Errorf("Fixed = %d, want 1", got)
	}

	other := Filters{BaselineStates: []string{"new"}}
	if got := view.Restrict(current.Filter(other), other).Comparison.Counts[Absent]; got != 0 {
		t.Errorf("Fixed = %d, want 0 when the filter does not name absent", got)
	}
}

func TestDisplayFingerprintIsTheOneTriageResolves(t *testing.T) {
	r := makeResult("a", Error, "a.java", 1, fp("source-sink-value", "trace-value"))
	report := makeReport(r)

	shown := fingerprintAbbrev(&report.Runs[0].Results[0], "")
	resolved, err := ResolvePrefix(report, DefaultIdentityKey, shown)
	if err != nil {
		t.Fatalf("the fingerprint the listing shows does not resolve: %v", err)
	}
	if got, _ := Identity(resolved, DefaultIdentityKey); got != "sink-of-source-sink-value" {
		t.Errorf("resolved %q, want the value under the default key", got)
	}
}
