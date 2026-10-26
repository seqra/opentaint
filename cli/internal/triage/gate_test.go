package triage

import (
	"testing"

	"github.com/seqra/opentaint/internal/sarif"
)

func result(ruleID string) sarif.Result {
	level := sarif.Error
	return sarif.Result{RuleID: &ruleID, Level: &level}
}
func report(results ...sarif.Result) *sarif.Report {
	return &sarif.Report{Runs: []sarif.Run{{Results: results}}}
}
func lvlptr(level sarif.Level) *sarif.Level { return &level }
func warn(ruleID string) sarif.Result {
	r := result(ruleID)
	r.Level = lvlptr(sarif.Warning)
	return r
}

func TestGateDisabledNeverTrips(t *testing.T) {
	rep := report(result("a"))
	count, tripped := Gate{}.Evaluate(rep)
	if tripped {
		t.Error("a disabled gate must never trip")
	}
	if count != 0 {
		t.Errorf("count: got %d, want 0", count)
	}
}

func TestGateCountsEveryFindingWithoutBaseline(t *testing.T) {
	rep := report(result("a"), warn("b"))
	count, tripped := Gate{Enabled: true}.Evaluate(rep)
	if !tripped || count != 2 {
		t.Errorf("got (%d, %v), want (2, true)", count, tripped)
	}
}

func TestGateRestrictsToSeverities(t *testing.T) {
	rep := report(result("a"), warn("b"))

	count, tripped := Gate{Enabled: true, Severities: []string{"error"}}.Evaluate(rep)
	if count != 1 || !tripped {
		t.Errorf("got (%d, %v), want (1, true)", count, tripped)
	}

	count, tripped = Gate{Enabled: true, Severities: []string{"note"}}.Evaluate(rep)
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
