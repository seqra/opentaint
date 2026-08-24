package cmd

import (
	"strings"
	"testing"

	"github.com/seqra/opentaint/internal/sarif"
)

func TestSingleJustificationRejectsMoreThanOne(t *testing.T) {
	got, err := singleJustification([]string{"first reason", "second reason"})
	if err == nil {
		t.Fatalf("two justifications were accepted, returning %q", got)
	}
	if !strings.Contains(err.Error(), "one run records one reason") {
		t.Errorf("unhelpful error: %v", err)
	}
}

func TestSingleJustificationPassesThroughOneOrNone(t *testing.T) {
	if got, err := singleJustification(nil); got != "" || err != nil {
		t.Errorf("got (%q, %v), want empty", got, err)
	}
	if got, err := singleJustification([]string{"why"}); got != "why" || err != nil {
		t.Errorf("got (%q, %v), want (\"why\", nil)", got, err)
	}
}

func TestRequireBaselineStatesRefusesAFilterThatCannotMatch(t *testing.T) {
	report := &sarif.Report{Runs: []sarif.Run{{Results: []sarif.Result{{}}}}}

	err := requireBaselineStates(report, []string{"new"}, "")
	if err == nil {
		t.Fatal("filtering a report with no baseline states silently reported nothing")
	}
	if !strings.Contains(err.Error(), "--write-baseline-state") {
		t.Errorf("the error does not say how to get states: %v", err)
	}

	if err := requireBaselineStates(report, []string{"new"}, "baseline.sarif"); err != nil {
		t.Errorf("a comparison supplies the states, so this must pass: %v", err)
	}
	if err := requireBaselineStates(report, nil, ""); err != nil {
		t.Errorf("no filter, nothing to require: %v", err)
	}
}

func TestRequireBaselineStatesAcceptsAPersistedReport(t *testing.T) {
	state := sarif.New
	report := &sarif.Report{Runs: []sarif.Run{{Results: []sarif.Result{{BaselineState: &state}}}}}
	if err := requireBaselineStates(report, []string{"new"}, ""); err != nil {
		t.Errorf("a report carrying states filters without a baseline: %v", err)
	}
}

func TestRequireBaselineStatesAbsentAlwaysNeedsABaseline(t *testing.T) {
	// Persisted states satisfy the guard for new/unchanged/updated, but absent
	// findings are never written into a report, so the filter can only ever be
	// served by a live comparison.
	state := sarif.New
	report := &sarif.Report{Runs: []sarif.Run{{Results: []sarif.Result{{BaselineState: &state}}}}}

	err := requireBaselineStates(report, []string{"absent"}, "")
	if err == nil {
		t.Fatal("absent without --baseline silently lists nothing and must be refused")
	}
	if !strings.Contains(err.Error(), "--baseline") {
		t.Errorf("the error should point at --baseline: %v", err)
	}

	if err := requireBaselineStates(report, []string{"absent"}, "baseline.sarif"); err != nil {
		t.Errorf("with --baseline the comparison supplies absent findings: %v", err)
	}
	if err := requireBaselineStates(report, []string{"new", "absent"}, ""); err == nil {
		t.Error("a mixed filter naming absent still needs --baseline")
	}
}
