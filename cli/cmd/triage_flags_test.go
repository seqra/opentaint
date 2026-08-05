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
