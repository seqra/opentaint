package triage

import (
	"testing"

	"github.com/seqra/opentaint/internal/sarif"
)

func warn(ruleID, identity string) sarif.Result {
	r := result(ruleID, identity, "trace-"+identity)
	r.Level = lvlptr(sarif.Warning)
	return r
}

func TestGateDisabledNeverTrips(t *testing.T) {
	rep := report(result("a", "id-a", "trace-a"))
	out, _ := Apply(rep, Options{})
	count, tripped := Gate{}.Evaluate(rep, out.View)
	if tripped {
		t.Error("a disabled gate must never trip")
	}
	if count != 0 {
		t.Errorf("count: got %d, want 0", count)
	}
}

func TestGateCountsEveryFindingWithoutBaseline(t *testing.T) {
	rep := report(result("a", "id-a", "trace-a"), warn("b", "id-b"))
	out, _ := Apply(rep, Options{})
	count, tripped := Gate{Enabled: true}.Evaluate(rep, out.View)
	if !tripped || count != 2 {
		t.Errorf("got (%d, %v), want (2, true)", count, tripped)
	}
}

func TestGateIgnoresSuppressedFindings(t *testing.T) {
	rep := report(result("a", "id-aaa", "trace-a"), result("b", "id-bbb", "trace-b"))
	out, err := Apply(rep, Options{Accept: []string{"id-aaa"}, Justification: "why"})
	if err != nil {
		t.Fatal(err)
	}
	count, tripped := Gate{Enabled: true}.Evaluate(rep, out.View)
	if count != 1 || !tripped {
		t.Errorf("got (%d, %v), want (1, true)", count, tripped)
	}
}

func TestGateIgnoresDeferredFindings(t *testing.T) {
	rep := report(result("a", "id-aaa", "trace-a"))
	out, err := Apply(rep, Options{Defer: []string{"id-aaa"}, Justification: "not now"})
	if err != nil {
		t.Fatal(err)
	}
	if _, tripped := (Gate{Enabled: true}).Evaluate(rep, out.View); tripped {
		t.Error("a deferred finding must not trip the gate")
	}
}

func TestGateWithBaselineCountsOnlyNewFindings(t *testing.T) {
	baseline := report(result("old", "id-old", "trace-old"))
	rep := report(result("old", "id-old", "trace-old"), result("new", "id-new", "trace-new"))
	out, err := Apply(rep, Options{Baseline: baseline})
	if err != nil {
		t.Fatal(err)
	}
	count, tripped := Gate{Enabled: true}.Evaluate(rep, out.View)
	if count != 1 || !tripped {
		t.Errorf("got (%d, %v), want (1, true): only the new finding counts", count, tripped)
	}
}

func TestGateWithBaselineDoesNotTripWhenNothingIsNew(t *testing.T) {
	baseline := report(result("old", "id-old", "trace-old"))
	rep := report(result("old", "id-old", "trace-old"))
	out, err := Apply(rep, Options{Baseline: baseline})
	if err != nil {
		t.Fatal(err)
	}
	if _, tripped := (Gate{Enabled: true}).Evaluate(rep, out.View); tripped {
		t.Error("an unchanged report must not trip the gate")
	}
}

func TestGateDoesNotCountUpdatedFindings(t *testing.T) {
	baseline := report(result("a", "id-a", "trace-old"))
	rep := report(result("a", "id-a", "trace-new"))
	out, err := Apply(rep, Options{Baseline: baseline})
	if err != nil {
		t.Fatal(err)
	}
	if _, tripped := (Gate{Enabled: true}).Evaluate(rep, out.View); tripped {
		t.Error("an updated finding is the same accepted vulnerability through a new path, not a new finding")
	}
}

func TestGateCountsUncomparableFindings(t *testing.T) {
	// A finding with no identity fingerprint cannot be matched against the
	// baseline. Fail closed: it is reported and it counts.
	baseline := report(result("old", "id-old", "trace-old"))
	nofp := sarif.Result{RuleID: strptr("nofp"), Level: lvlptr(sarif.Error)}
	rep := report(result("old", "id-old", "trace-old"))
	rep.Runs[0].Results = append(rep.Runs[0].Results, nofp)

	out, err := Apply(rep, Options{Baseline: baseline})
	if err != nil {
		t.Fatal(err)
	}
	count, tripped := Gate{Enabled: true}.Evaluate(rep, out.View)
	if count != 1 || !tripped {
		t.Errorf("got (%d, %v), want (1, true)", count, tripped)
	}
}

func TestGateRestrictsToSeverities(t *testing.T) {
	rep := report(result("a", "id-a", "trace-a"), warn("b", "id-b"))
	out, _ := Apply(rep, Options{})

	count, tripped := Gate{Enabled: true, Severities: []string{"error"}}.Evaluate(rep, out.View)
	if count != 1 || !tripped {
		t.Errorf("got (%d, %v), want (1, true)", count, tripped)
	}

	count, tripped = Gate{Enabled: true, Severities: []string{"note"}}.Evaluate(rep, out.View)
	if count != 0 || tripped {
		t.Errorf("got (%d, %v), want (0, false)", count, tripped)
	}
}

func TestParseGateSeverities(t *testing.T) {
	if _, err := ParseGateSeverities([]string{"error", "warning"}); err != nil {
		t.Errorf("unexpected error: %v", err)
	}
	if _, err := ParseGateSeverities([]string{"critical"}); err == nil {
		t.Error("expected an error for an unknown severity")
	}
}

func TestParseGateSeveritiesSplitsCommaSeparated(t *testing.T) {
	got, err := ParseGateSeverities([]string{"error,warning"})
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(got) != 2 || got[0] != "error" || got[1] != "warning" {
		t.Errorf("got %v, want [error warning]", got)
	}
}

func TestParseGateSeveritiesMixesCommaAndRepeatedFlags(t *testing.T) {
	got, err := ParseGateSeverities([]string{"error, warning", "note"})
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(got) != 3 {
		t.Errorf("got %v, want error warning note", got)
	}
}

func TestParseGateSeveritiesRejectsBadTokenInsideAList(t *testing.T) {
	if _, err := ParseGateSeverities([]string{"error,bogus"}); err == nil {
		t.Error("expected an error for a bad token in a comma list")
	}
}

func TestParseGateSeveritiesIgnoresEmptyTokens(t *testing.T) {
	got, err := ParseGateSeverities([]string{"error,,warning,"})
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(got) != 2 {
		t.Errorf("got %v, want [error warning]", got)
	}
}
