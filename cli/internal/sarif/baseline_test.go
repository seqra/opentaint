package sarif

import (
	"regexp"
	"testing"
)

// fps builds a partialFingerprints map from all three hashes, as the analyzer
// emits them. An empty value leaves that key out.
func fps(sink, sourceSink, trace string) map[string]string {
	m := map[string]string{}
	for key, value := range map[string]string{
		SinkFingerprintKey:       sink,
		SourceSinkFingerprintKey: sourceSink,
		TraceFingerprintKey:      trace,
	} {
		if value != "" {
			m[key] = value
		}
	}
	return m
}

// fp is fps for a finding whose sink is implied by its source/sink hash, which
// is the common case: one sink, one source, one finding.
func fp(sourceSink, trace string) map[string]string {
	sink := ""
	if sourceSink != "" {
		sink = "sink-of-" + sourceSink
	}
	return fps(sink, sourceSink, trace)
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

	cmp, err := CompareToBaseline(current, baseline)
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

func TestCompareTreatsMissingTraceHashAsUnchanged(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "")))
	current := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "")))

	cmp, err := CompareToBaseline(current, baseline)
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

	cmp, err := CompareToBaseline(current, baseline)
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

	cmp, err := CompareToBaseline(current, baseline)
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

	_, err := CompareToBaseline(current, baseline)
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

	cmp, err := CompareToBaseline(current, baseline)
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

	cmp, err := CompareToBaseline(current, baseline)
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
	guid := "11111111-2222-3333-4444-555555555555"
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	baseline.Runs[0].AutomationDetails = &RunAutomationDetails{GUID: &guid}
	current := makeReport(makeResult("nofp", Error, "b.java", 2, nil))

	cmp, err := CompareToBaseline(current, baseline)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	cmp.Apply(current)

	if current.Results()[0].BaselineState != nil {
		t.Errorf("unmatchable result was annotated: %v", *current.Results()[0].BaselineState)
	}
	if current.Runs[0].BaselineGUID != nil {
		t.Errorf("baselineGuid was written although a result has no baselineState: %q", *current.Runs[0].BaselineGUID)
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

	cmp, err := CompareToBaseline(current, baseline)
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

	cmp, err := CompareToBaseline(current, baseline)
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
		t.Error("the baseline result itself was stamped, but only the copy may be")
	}
}

// Under the default sink identity, a finding that keeps its sink but gains a
// different source is "updated", and the report must be able to say which.
func TestChangeUnderSinkIdentityNamesWhatMoved(t *testing.T) {
	baseline := makeReport(
		makeResult("a", Error, "a.java", 1, fps("sink-a", "src-a", "trace-a")),
		makeResult("b", Error, "b.java", 2, fps("sink-b", "src-b", "trace-b")),
		makeResult("c", Error, "c.java", 3, fps("sink-c", "src-c", "trace-c")),
	)
	current := makeReport(
		makeResult("a", Error, "a.java", 1, fps("sink-a", "src-a", "trace-a")),        // nothing moved
		makeResult("b", Error, "b.java", 2, fps("sink-b", "src-b-other", "trace-b2")), // source moved
		makeResult("c", Error, "c.java", 3, fps("sink-c", "src-c", "trace-c-longer")), // path moved
	)

	cmp, err := CompareToBaseline(current, baseline)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}

	results := current.Results()
	for _, tc := range []struct {
		name  string
		idx   int
		state BaselineState
		want  Change
	}{
		{"nothing moved", 0, Unchanged, ChangeNone},
		{"source moved", 1, Updated, ChangeSource},
		{"path moved", 2, Updated, ChangePath},
	} {
		if got := cmp.StateOf(results[tc.idx]); got != tc.state {
			t.Errorf("%s: state = %q, want %q", tc.name, got, tc.state)
		}
		if got := cmp.ChangeOf(results[tc.idx]); got != tc.want {
			t.Errorf("%s: change = %q, want %q", tc.name, got, tc.want)
		}
	}

	if got := cmp.ChangeCounts[ChangeSource]; got != 1 {
		t.Errorf("source-changed count = %d, want 1", got)
	}
	if got := cmp.ChangeCounts[ChangePath]; got != 1 {
		t.Errorf("path-changed count = %d, want 1", got)
	}
	if got := cmp.Counts[Updated]; got != 2 {
		t.Errorf("updated count = %d, want 2 (every change is still one SARIF state)", got)
	}
}

// A source that moves drags the trace with it. The report names the source,
// because that is the more meaningful of the two.
func TestChangeReportsTheCoarsestThingThatMoved(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fps("sink-a", "src-a", "trace-a")))
	current := makeReport(makeResult("a", Error, "a.java", 1, fps("sink-a", "src-z", "trace-z")))

	cmp, err := CompareToBaseline(current, baseline)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	if got := cmp.ChangeOf(current.Results()[0]); got != ChangeSource {
		t.Errorf("change = %q, want %q", got, ChangeSource)
	}
}

// Matching each refining hash against a different duplicate is not enough to
// prove that the current finding is unchanged. The source/trace pair must have
// existed together on one baseline result.
func TestChangeUnderDoesNotMixFingerprintsAcrossBaselineDuplicates(t *testing.T) {
	baseline := makeReport(
		makeResult("a", Error, "a.java", 1, fps("sink-a", "source-1", "trace-1")),
		makeResult("a", Error, "a.java", 1, fps("sink-a", "source-2", "trace-2")),
	)
	current := makeReport(
		makeResult("a", Error, "a.java", 1, fps("sink-a", "source-1", "trace-2")),
	)

	cmp, err := CompareToBaseline(current, baseline)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	if got := cmp.StateOf(current.Results()[0]); got != Updated {
		t.Errorf("state = %q, want updated: no baseline result has source-1 and trace-2 together", got)
	}
	if got := cmp.ChangeOf(current.Results()[0]); got != ChangePath {
		t.Errorf("change = %q, want %q", got, ChangePath)
	}
}

// A new finding of the same rule in the same file is the hint that the sink
// hash itself drifted.
func TestRemnantDriftedNeedsANewSameRuleFindingInTheSameFile(t *testing.T) {
	baseline := makeReport(
		makeResult("a", Error, "a.java", 10, fps("sink-old", "src-a", "trace-a")),
		makeResult("b", Error, "b.java", 20, fps("sink-gone", "src-b", "trace-b")),
	)
	current := makeReport(
		makeResult("a", Error, "a.java", 12, fps("sink-new", "src-a2", "trace-a2")),
	)

	cmp, err := CompareToBaseline(current, baseline)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	if len(cmp.Absent) != 2 {
		t.Fatalf("absent = %d, want 2", len(cmp.Absent))
	}
	for _, r := range cmp.Absent {
		want := RemnantNone
		if *r.RuleID == "a" {
			want = RemnantDrifted
		}
		if got := cmp.RemnantOf(r); got != want {
			t.Errorf("rule %s: remnant = %q, want %q", *r.RuleID, got, want)
		}
	}
}

// Only new current findings hint at a move. A finding that matched the
// baseline is accounted for and says nothing about the absent one.
func TestRemnantIgnoresMatchedFindingsOfTheSameRule(t *testing.T) {
	baseline := makeReport(
		makeResult("a", Error, "a.java", 10, fps("sink-kept", "src-a", "trace-a")),
		makeResult("a", Error, "a.java", 20, fps("sink-gone", "src-b", "trace-b")),
	)
	current := makeReport(
		makeResult("a", Error, "a.java", 10, fps("sink-kept", "src-a", "trace-a")),
	)

	cmp, err := CompareToBaseline(current, baseline)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	if len(cmp.Absent) != 1 {
		t.Fatalf("absent = %d, want 1", len(cmp.Absent))
	}
	if got := cmp.RemnantOf(cmp.Absent[0]); got != RemnantNone {
		t.Errorf("remnant = %q, want none: the same-rule finding was matched, not new", got)
	}
}

// The remnant lookup runs by identity, so the display copies that WithAbsent
// stamps resolve to the same remnant as the baseline results themselves.
func TestRemnantResolvesOnDisplayCopies(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fps("sink-old", "src-old", "trace-old")))
	current := makeReport(makeResult("a", Error, "a.java", 4, fps("sink-new", "src-new", "trace-new")))

	cmp, err := CompareToBaseline(current, baseline)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	listing := current.WithAbsent(cmp.Absent)
	copyOfGone := listing.Results()[1]
	if got := cmp.RemnantOf(copyOfGone); got != RemnantDrifted {
		t.Errorf("remnant on copy = %q, want %q", got, RemnantDrifted)
	}
	if got := cmp.StateNote(copyOfGone); got != "possibly drifted" {
		t.Errorf("state note = %q, want %q", got, "possibly drifted")
	}
}

func TestStateNoteNamesWhatMovedUnderUpdated(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fps("sink-a", "src-a", "trace-a")))
	current := makeReport(makeResult("a", Error, "a.java", 1, fps("sink-a", "src-b", "trace-b")))

	cmp, err := CompareToBaseline(current, baseline)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	cmp.Apply(current)
	if got := cmp.StateNote(current.Results()[0]); got != "source changed" {
		t.Errorf("state note = %q, want %q", got, "source changed")
	}
}

func TestCheckBaselineIdentity(t *testing.T) {
	if err := CheckBaselineIdentity(&Report{}); err != nil {
		t.Errorf("an empty baseline is comparable: %v", err)
	}
	carrying := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	if err := CheckBaselineIdentity(carrying); err != nil {
		t.Errorf("baseline carries the identity fingerprint: %v", err)
	}
	traceOnly := makeReport(makeResult("a", Error, "a.java", 1, fp("", "trace-a")))
	if err := CheckBaselineIdentity(traceOnly); err == nil {
		t.Error("expected an error for a baseline without the identity fingerprint")
	}
}
