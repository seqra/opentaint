package triage

import (
	"strings"
	"testing"

	"github.com/seqra/opentaint/internal/sarif"
)

func strptr(s string) *string           { return &s }
func lvlptr(l sarif.Level) *sarif.Level { return &l }

func result(ruleID, identity string, trace string) sarif.Result {
	return sarif.Result{
		RuleID: strptr(ruleID),
		Level:  lvlptr(sarif.Error),
		Locations: []sarif.Location{{
			PhysicalLocation: &sarif.PhysicalLocation{
				ArtifactLocation: &sarif.ArtifactLocation{URI: strptr(ruleID + ".java")},
			},
		}},
		PartialFingerprints: map[string]string{
			sarif.SinkFingerprintKey:       identity,
			sarif.SourceSinkFingerprintKey: identity,
			sarif.TraceFingerprintKey:      trace,
		},
	}
}

func report(results ...sarif.Result) *sarif.Report {
	return &sarif.Report{Runs: []sarif.Run{{Results: results}}}
}

func TestApplyWithNoOptionsChangesNothing(t *testing.T) {
	r := report(result("a", "id-a", "trace-a"))
	out, err := Apply(r, Options{})
	if err != nil {
		t.Fatalf("apply: %v", err)
	}
	if out.Changed {
		t.Error("expected no change")
	}
	if out.View.Comparison != nil {
		t.Error("expected no comparison without a baseline")
	}
}

func TestApplyInheritsSuppressionsFromBaseline(t *testing.T) {
	base := result("a", "id-a", "trace-a")
	if err := sarif.Accept(&base, "admin-only input"); err != nil {
		t.Fatal(err)
	}
	current := report(result("a", "id-a", "trace-a"), result("b", "id-b", "trace-b"))

	out, err := Apply(current, Options{Baseline: report(base)})
	if err != nil {
		t.Fatalf("apply: %v", err)
	}
	if out.View.Inherited != 1 {
		t.Errorf("inherited: got %d, want 1", out.View.Inherited)
	}
	if !sarif.IsSuppressed(current.Results()[0]) {
		t.Error("matching finding should have inherited the suppression")
	}
	if !out.Changed {
		t.Error("inheriting a suppression changes the report")
	}
}

func TestApplyComparesButDoesNotWriteStateByDefault(t *testing.T) {
	current := report(result("a", "id-a", "trace-a"), result("b", "id-b", "trace-b"))
	out, err := Apply(current, Options{Baseline: report(result("a", "id-a", "trace-a"))})
	if err != nil {
		t.Fatalf("apply: %v", err)
	}
	if out.View.Comparison.Counts[sarif.New] != 1 {
		t.Errorf("expected 1 new, got %d", out.View.Comparison.Counts[sarif.New])
	}
	for _, r := range current.Results() {
		if r.BaselineState != nil {
			t.Error("baselineState must not be written without WriteBaselineState")
		}
	}
	if out.View.StateWritten {
		t.Error("StateWritten should be false")
	}
	if out.Changed {
		t.Error("a comparison alone does not change the report")
	}
}

func TestApplyWritesStateWhenAsked(t *testing.T) {
	current := report(result("a", "id-a", "trace-a"))
	out, err := Apply(current, Options{
		Baseline:           report(result("a", "id-a", "trace-a")),
		WriteBaselineState: true,
	})
	if err != nil {
		t.Fatalf("apply: %v", err)
	}
	if current.Results()[0].BaselineState == nil {
		t.Fatal("baselineState not written")
	}
	if !out.View.StateWritten || !out.Changed {
		t.Error("writing state marks the report changed")
	}
	if current.RunGUID() == "" {
		t.Error("a written report must be citable as a baseline: expected a run guid")
	}
}

func TestApplyAcceptsByFingerprintPrefix(t *testing.T) {
	current := report(result("a", "id-aaa111", "trace-a"), result("b", "id-bbb222", "trace-b"))
	out, err := Apply(current, Options{
		Accept:        []string{"id-aaa"},
		Justification: "sink is a constant",
	})
	if err != nil {
		t.Fatalf("apply: %v", err)
	}
	if out.View.Added != 1 {
		t.Errorf("added: got %d, want 1", out.View.Added)
	}
	first := current.Results()[0]
	if !sarif.IsSuppressed(first) || sarif.StatusOf(first) != "accepted" {
		t.Errorf("expected an accepted suppression, got %q", sarif.StatusOf(first))
	}
	if sarif.IsSuppressed(current.Results()[1]) {
		t.Error("the other finding must be untouched")
	}
}

func TestApplyDefersByFingerprintPrefix(t *testing.T) {
	current := report(result("a", "id-aaa111", "trace-a"))
	if _, err := Apply(current, Options{Defer: []string{"id-aaa"}, Justification: "waiting on OT-412"}); err != nil {
		t.Fatalf("apply: %v", err)
	}
	if got := sarif.StatusOf(current.Results()[0]); got != "underReview" {
		t.Errorf("status: got %q, want underReview", got)
	}
}

func TestApplyUnsuppresses(t *testing.T) {
	r := result("a", "id-aaa111", "trace-a")
	if err := sarif.Accept(&r, "was accepted"); err != nil {
		t.Fatal(err)
	}
	current := report(r)

	out, err := Apply(current, Options{Unsuppress: []string{"id-aaa"}})
	if err != nil {
		t.Fatalf("apply: %v", err)
	}
	if sarif.IsSuppressed(current.Results()[0]) {
		t.Error("expected the suppression to be removed")
	}
	if !out.Changed {
		t.Error("removing a suppression changes the report")
	}
}

func TestApplyRequiresJustificationForAccept(t *testing.T) {
	current := report(result("a", "id-aaa111", "trace-a"))
	_, err := Apply(current, Options{Accept: []string{"id-aaa"}})
	if err == nil || !strings.Contains(err.Error(), "justification") {
		t.Errorf("expected a justification error, got %v", err)
	}
	if sarif.IsSuppressed(current.Results()[0]) {
		t.Error("nothing should be suppressed when validation fails")
	}
}

func TestApplyRejectsUnknownFingerprint(t *testing.T) {
	current := report(result("a", "id-aaa111", "trace-a"))
	_, err := Apply(current, Options{Accept: []string{"zzz"}, Justification: "why"})
	if err == nil {
		t.Error("expected an error for an unmatched fingerprint")
	}
}

func TestApplyRejectsAmbiguousFingerprint(t *testing.T) {
	current := report(result("a", "id-aaa111", "trace-a"), result("b", "id-aaa222", "trace-b"))
	_, err := Apply(current, Options{Accept: []string{"id-aaa"}, Justification: "why"})
	if err == nil || !strings.Contains(err.Error(), "ambiguous") {
		t.Errorf("expected an ambiguity error, got %v", err)
	}
}

func TestApplyPropagatesBaselineKeyMismatch(t *testing.T) {
	baseline := &sarif.Report{Runs: []sarif.Run{{Results: []sarif.Result{{
		RuleID:              strptr("a"),
		PartialFingerprints: map[string]string{"someOtherKey/v1": "x"},
	}}}}}
	_, err := Apply(report(result("a", "id-a", "trace-a")), Options{Baseline: baseline})
	if err == nil {
		t.Error("expected an error when the baseline lacks the identity key")
	}
}

func TestApplySuppressionStatsCoverTheWholeReport(t *testing.T) {
	current := report(result("a", "id-aaa", "trace-a"), result("b", "id-bbb", "trace-b"))
	out, err := Apply(current, Options{Accept: []string{"id-aaa"}, Justification: "why"})
	if err != nil {
		t.Fatalf("apply: %v", err)
	}
	if out.View.Suppressions.Total != 2 || out.View.Suppressions.Suppressed != 1 {
		t.Errorf("stats: got %+v", out.View.Suppressions)
	}
}

func TestApplyReadOnlyAnnotatesInMemoryWithoutClaimingToWrite(t *testing.T) {
	// summary never writes the report, but it still needs baselineState on the
	// in-memory copy so that --baseline-state can filter on it.
	current := report(result("a", "id-a", "trace-a"), result("b", "id-b", "trace-b"))
	out, err := Apply(current, Options{
		Baseline: report(result("a", "id-a", "trace-a")),
		ReadOnly: true,
	})
	if err != nil {
		t.Fatalf("apply: %v", err)
	}
	states := []string{}
	for _, r := range current.Results() {
		if r.BaselineState == nil {
			t.Fatal("read-only mode must still annotate the in-memory report")
		}
		states = append(states, string(*r.BaselineState))
	}
	if states[0] != "unchanged" || states[1] != "new" {
		t.Errorf("states: got %v", states)
	}
	if out.Changed {
		t.Error("read-only mode must never mark the report as needing a write")
	}
	if out.View.StateWritten {
		t.Error("read-only mode must not claim the state was persisted")
	}
	if !out.View.ReadOnly {
		t.Error("the view should record that nothing will be written")
	}
}

func TestApplyReadOnlyStillInheritsSuppressions(t *testing.T) {
	base := result("a", "id-a", "trace-a")
	if err := sarif.Accept(&base, "admin-only"); err != nil {
		t.Fatal(err)
	}
	current := report(result("a", "id-a", "trace-a"))
	out, err := Apply(current, Options{Baseline: report(base), ReadOnly: true})
	if err != nil {
		t.Fatal(err)
	}
	if !sarif.IsSuppressed(current.Results()[0]) {
		t.Error("read-only display must still show inherited suppressions")
	}
	if out.Changed {
		t.Error("read-only mode must not mark the report as changed")
	}
}
