package sarif

import (
	"regexp"
	"testing"
)

// fp builds a partialFingerprints map from a source/sink hash and a trace hash.
func fp(sourceSink, trace string) map[string]string {
	m := map[string]string{}
	if sourceSink != "" {
		m[SourceSinkFingerprintKey] = sourceSink
	}
	if trace != "" {
		m[TraceFingerprintKey] = trace
	}
	return m
}

func TestCompareClassifiesNewUnchangedUpdatedAbsent(t *testing.T) {
	baseline := makeReport(
		makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")),
		makeResult("b", Error, "b.java", 2, fp("id-b", "trace-b")),
		makeResult("gone", Error, "c.java", 3, fp("id-gone", "trace-gone")),
	)
	current := makeReport(
		makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")),       // unchanged
		makeResult("b", Error, "b.java", 9, fp("id-b", "trace-b-moved")), // updated
		makeResult("fresh", Error, "d.java", 4, fp("id-fresh", "trace-fresh")),
	)

	cmp, err := CompareToBaseline(current, baseline, SourceSinkFingerprintKey)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}

	results := current.Results()
	if got := cmp.StateOf(results[0]); got != Unchanged {
		t.Errorf("first result: got %q, want unchanged", got)
	}
	if got := cmp.StateOf(results[1]); got != Updated {
		t.Errorf("second result: got %q, want updated", got)
	}
	if got := cmp.StateOf(results[2]); got != New {
		t.Errorf("third result: got %q, want new", got)
	}
	if cmp.Counts[Absent] != 1 {
		t.Errorf("absent count: got %d, want 1", cmp.Counts[Absent])
	}
	if len(cmp.Absent) != 1 || *cmp.Absent[0].RuleID != "gone" {
		t.Errorf("absent results: got %v", cmp.Absent)
	}
	for state, want := range map[BaselineState]int{New: 1, Unchanged: 1, Updated: 1} {
		if cmp.Counts[state] != want {
			t.Errorf("%s count: got %d, want %d", state, cmp.Counts[state], want)
		}
	}
}

func TestCompareWithTraceKeyNeverReportsUpdated(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	current := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))

	cmp, err := CompareToBaseline(current, baseline, TraceFingerprintKey)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	if got := cmp.StateOf(current.Results()[0]); got != Unchanged {
		t.Errorf("got %q, want unchanged", got)
	}
}

func TestCompareTreatsMissingTraceHashAsUnchanged(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "")))
	current := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "")))

	cmp, err := CompareToBaseline(current, baseline, SourceSinkFingerprintKey)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	if got := cmp.StateOf(current.Results()[0]); got != Unchanged {
		t.Errorf("got %q, want unchanged", got)
	}
}

func TestCompareCountsUnmatchableResultsSeparately(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	current := makeReport(
		makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")),
		makeResult("nofp", Error, "b.java", 2, nil),
	)

	cmp, err := CompareToBaseline(current, baseline, SourceSinkFingerprintKey)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	if cmp.Unmatchable != 1 {
		t.Errorf("unmatchable: got %d, want 1", cmp.Unmatchable)
	}
	if got := cmp.StateOf(current.Results()[1]); got != "" {
		t.Errorf("unmatchable result should have no state, got %q", got)
	}
	if cmp.Counts[New] != 0 {
		t.Errorf("unmatchable must not be counted as new, got %d", cmp.Counts[New])
	}
}

func TestCompareDuplicateIdentitiesBothMatch(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	current := makeReport(
		makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")),
		makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")),
	)

	cmp, err := CompareToBaseline(current, baseline, SourceSinkFingerprintKey)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	if cmp.Counts[Unchanged] != 2 {
		t.Errorf("both duplicates should match: got %d unchanged", cmp.Counts[Unchanged])
	}
	if cmp.Counts[Absent] != 0 {
		t.Errorf("baseline entry was matched, want 0 absent, got %d", cmp.Counts[Absent])
	}
}

func TestCompareEmptyBaselineMakesEverythingNew(t *testing.T) {
	cmp, err := CompareToBaseline(
		makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a"))),
		&Report{},
		SourceSinkFingerprintKey,
	)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	if cmp.Counts[New] != 1 {
		t.Errorf("got %d new, want 1", cmp.Counts[New])
	}
}

func TestCompareRejectsBaselineWithoutTheIdentityKey(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("", "trace-a")))
	current := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))

	_, err := CompareToBaseline(current, baseline, SourceSinkFingerprintKey)
	if err == nil {
		t.Fatal("expected an error when no baseline result carries the identity key")
	}
}

func TestCompareEmptyBaselineIsNotAKeyMismatch(t *testing.T) {
	// A baseline with zero results has no fingerprints either, but that is a
	// legitimate "nothing was known before", not a key mismatch.
	if _, err := CompareToBaseline(
		makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a"))),
		&Report{Runs: []Run{{}}},
		SourceSinkFingerprintKey,
	); err != nil {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestApplyWritesBaselineStateAndGUID(t *testing.T) {
	guid := "11111111-2222-3333-4444-555555555555"
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	baseline.Runs[0].AutomationDetails = &RunAutomationDetails{GUID: &guid}
	current := makeReport(
		makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")),
		makeResult("fresh", Error, "b.java", 2, fp("id-fresh", "trace-fresh")),
	)

	cmp, err := CompareToBaseline(current, baseline, SourceSinkFingerprintKey)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	cmp.Apply(current)

	results := current.Results()
	if results[0].BaselineState == nil || *results[0].BaselineState != Unchanged {
		t.Errorf("first result state not written: %v", results[0].BaselineState)
	}
	if results[1].BaselineState == nil || *results[1].BaselineState != New {
		t.Errorf("second result state not written: %v", results[1].BaselineState)
	}
	if current.Runs[0].BaselineGUID == nil || *current.Runs[0].BaselineGUID != guid {
		t.Errorf("baselineGuid not written: %v", current.Runs[0].BaselineGUID)
	}
}

func TestApplyOmitsBaselineGUIDWhenBaselineHasNone(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	current := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))

	cmp, err := CompareToBaseline(current, baseline, SourceSinkFingerprintKey)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	cmp.Apply(current)

	if current.Runs[0].BaselineGUID != nil {
		t.Errorf("expected no baselineGuid, got %q", *current.Runs[0].BaselineGUID)
	}
	if current.Results()[0].BaselineState == nil {
		t.Error("states should still be written without a baseline guid")
	}
}

func TestApplyLeavesUnmatchableResultsUnannotated(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	current := makeReport(makeResult("nofp", Error, "b.java", 2, nil))

	cmp, err := CompareToBaseline(current, baseline, SourceSinkFingerprintKey)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	cmp.Apply(current)

	if current.Results()[0].BaselineState != nil {
		t.Errorf("unmatchable result was annotated: %v", *current.Results()[0].BaselineState)
	}
}

func TestEnsureRunGUIDsStampsMissingOnesOnly(t *testing.T) {
	existing := "11111111-2222-3333-4444-555555555555"
	report := &Report{Runs: []Run{
		{AutomationDetails: &RunAutomationDetails{GUID: &existing}},
		{},
	}}

	EnsureRunGUIDs(report)

	if report.Runs[0].AutomationDetails.GUID == nil || *report.Runs[0].AutomationDetails.GUID != existing {
		t.Error("existing guid was overwritten")
	}
	if report.Runs[1].AutomationDetails == nil || report.Runs[1].AutomationDetails.GUID == nil {
		t.Fatal("missing guid was not stamped")
	}
	uuidV4 := regexp.MustCompile(`^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$`)
	if got := *report.Runs[1].AutomationDetails.GUID; !uuidV4.MatchString(got) {
		t.Errorf("stamped guid %q is not a v4 uuid", got)
	}
}

func TestReportBaselineGUIDReadsFirstRun(t *testing.T) {
	guid := "11111111-2222-3333-4444-555555555555"
	report := &Report{Runs: []Run{{AutomationDetails: &RunAutomationDetails{GUID: &guid}}}}
	if got := report.RunGUID(); got != guid {
		t.Errorf("got %q, want %q", got, guid)
	}
	if got := (&Report{Runs: []Run{{}}}).RunGUID(); got != "" {
		t.Errorf("got %q, want empty", got)
	}
}

// withRules declares the rules a run executed, which is how a comparison tells
// "this rule found nothing" from "this rule never ran".
func withRules(report *Report, ruleIDs ...string) *Report {
	for i := range report.Runs {
		var rules []ReportingDescriptor
		for _, id := range ruleIDs {
			rules = append(rules, ReportingDescriptor{ID: id})
		}
		report.Runs[i].Tool.Driver.Rules = rules
	}
	return report
}

func TestCompareKeepsExcludedRuleOutOfFixed(t *testing.T) {
	baseline := makeReport(
		makeResult("kept", Error, "a.java", 1, fp("id-kept", "trace-kept")),
		makeResult("excluded", Error, "b.java", 2, fp("id-excluded", "trace-excluded")),
		makeResult("kept", Error, "c.java", 3, fp("id-fixed", "trace-fixed")),
	)
	// The current scan ran only "kept": "excluded" produced nothing because it
	// never loaded, while id-fixed genuinely disappeared.
	current := withRules(makeReport(
		makeResult("kept", Error, "a.java", 1, fp("id-kept", "trace-kept")),
	), "kept")

	cmp, err := CompareToBaseline(current, baseline, SourceSinkFingerprintKey)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}

	if got := cmp.Counts[Absent]; got != 1 {
		t.Errorf("Fixed = %d, want 1 (only the finding whose rule actually ran)", got)
	}
	if got := len(cmp.NotRun); got != 1 {
		t.Fatalf("NotRun = %d, want 1", got)
	}
	if got := *cmp.NotRun[0].RuleID; got != "excluded" {
		t.Errorf("NotRun holds %q, want the excluded rule", got)
	}
}

func TestCompareTreatsMissingRuleListAsEverythingRan(t *testing.T) {
	// A report that declares no rules says nothing about what ran, so guessing
	// "excluded" would hide genuinely fixed findings.
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	current := makeReport()

	cmp, err := CompareToBaseline(current, baseline, SourceSinkFingerprintKey)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	if got := cmp.Counts[Absent]; got != 1 {
		t.Errorf("Fixed = %d, want 1", got)
	}
	if len(cmp.NotRun) != 0 {
		t.Errorf("NotRun = %d, want 0", len(cmp.NotRun))
	}
}

func TestWithAbsentAddsFixedFindingsForDisplayOnly(t *testing.T) {
	current := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	gone := makeResult("b", Error, "b.java", 2, fp("id-b", "trace-b"))

	listing := current.WithAbsent([]*Result{&gone})

	if got := len(listing.Results()); got != 2 {
		t.Fatalf("listing holds %d results, want 2", got)
	}
	if got := len(current.Results()); got != 1 {
		t.Errorf("the source report grew to %d results: WithAbsent must not mutate it", got)
	}
	added := listing.Results()[1]
	if added.BaselineState == nil || *added.BaselineState != Absent {
		t.Error("the added result is not marked absent")
	}
	if gone.BaselineState != nil {
		t.Error("the baseline result itself was stamped; only the copy may be")
	}
}
