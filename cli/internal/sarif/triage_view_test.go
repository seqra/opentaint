package sarif

import (
	"strings"
	"testing"
)

func newState(s BaselineState) *BaselineState { return &s }

func TestFilterByBaselineState(t *testing.T) {
	a := makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a"))
	a.BaselineState = newState(New)
	b := makeResult("b", Error, "b.java", 2, fp("id-b", "trace-b"))
	b.BaselineState = newState(Unchanged)
	c := makeResult("c", Error, "c.java", 3, fp("id-c", "trace-c"))
	report := makeReport(a, b, c)

	got := report.Filter(Filters{BaselineStates: []string{"new"}})
	if len(got.Runs[0].Results) != 1 || *got.Runs[0].Results[0].RuleID != "a" {
		t.Errorf("expected only the new finding, got %d results", len(got.Runs[0].Results))
	}

	got = report.Filter(Filters{BaselineStates: []string{"new", "unchanged"}})
	if len(got.Runs[0].Results) != 2 {
		t.Errorf("expected 2 results, got %d", len(got.Runs[0].Results))
	}
}

func TestFilterByBaselineStateIsCaseInsensitive(t *testing.T) {
	a := makeResult("a", Error, "a.java", 1, nil)
	a.BaselineState = newState(New)
	got := makeReport(a).Filter(Filters{BaselineStates: []string{" NEW "}})
	if len(got.Runs[0].Results) != 1 {
		t.Errorf("expected 1 result, got %d", len(got.Runs[0].Results))
	}
}

func TestParseBaselineStatesValidatesValues(t *testing.T) {
	if _, err := ParseBaselineStates([]string{"new", "absent"}); err != nil {
		t.Errorf("unexpected error: %v", err)
	}
	if _, err := ParseBaselineStates([]string{"nope"}); err == nil {
		t.Error("expected an error for an unknown baseline state")
	}
}

func TestPrintAllHidesSuppressedByDefault(t *testing.T) {
	rendered := renderListing(t, makeReport(
		suppressed("hidden.rule", "id-a", Accepted, "admin-only input"),
		makeResult("shown.rule", Error, "b.java", 2, fp("id-b", "trace-b")),
	), ListingOptions{MaxNestingLevel: -1})

	if strings.Contains(rendered, "hidden.rule") {
		t.Errorf("suppressed finding should be hidden by default:\n%s", rendered)
	}
	if !strings.Contains(rendered, "shown.rule") {
		t.Errorf("unsuppressed finding should be listed:\n%s", rendered)
	}
}

func TestPrintAllShowsSuppressedWithJustification(t *testing.T) {
	rendered := renderListing(t, makeReport(suppressed("hidden.rule", "id-a", Accepted, "admin-only input")), ListingOptions{MaxNestingLevel: -1, ShowSuppressed: true})

	if !strings.Contains(rendered, "hidden.rule") {
		t.Errorf("finding should be listed with ShowSuppressed:\n%s", rendered)
	}
	if !strings.Contains(rendered, "admin-only input") {
		t.Errorf("justification should be shown:\n%s", rendered)
	}
	if !strings.Contains(rendered, "accepted") {
		t.Errorf("status should be shown:\n%s", rendered)
	}
}

func TestPrintAllShowsBaselineState(t *testing.T) {
	r := makeResult("a.rule", Error, "a.java", 1, fp("id-a", "trace-a"))
	r.BaselineState = newState(New)
	rendered := renderListing(t, makeReport(r), ListingOptions{MaxNestingLevel: -1})

	if !strings.Contains(rendered, "Baseline") || !strings.Contains(rendered, "new") {
		t.Errorf("expected a baseline state field:\n%s", rendered)
	}
}

func TestPrintAllOmitsBaselineFieldWhenAbsent(t *testing.T) {
	rendered := renderListing(t, makeReport(makeResult("a.rule", Error, "a.java", 1, nil)),
		ListingOptions{MaxNestingLevel: -1})

	if strings.Contains(rendered, "Baseline") {
		t.Errorf("no baseline field expected without a comparison:\n%s", rendered)
	}
}

func TestPrintAllAllSuppressedRendersNothing(t *testing.T) {
	rendered := renderListing(t, makeReport(suppressed("hidden.rule", "id-a", Accepted, "why")),
		ListingOptions{MaxNestingLevel: -1})
	if strings.TrimSpace(rendered) != "" {
		t.Errorf("expected no output, got:\n%s", rendered)
	}
}
