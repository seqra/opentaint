package sarif

import (
	"strings"
	"testing"
)

func statusPtr(s Status) *Status { return &s }

// suppressed builds a result carrying one external suppression with the given
// status ("" means the status property is absent).
func suppressed(ruleID, sourceSink string, status Status, justification string) Result {
	r := makeResult(ruleID, Error, "a.java", 1, fp(sourceSink, "trace-"+sourceSink))
	s := Suppression{Kind: External, Justification: strptr(justification)}
	if status != "" {
		s.Status = statusPtr(status)
	}
	r.Suppressions = []Suppression{s}
	return r
}

func TestIsSuppressedReadRule(t *testing.T) {
	cases := []struct {
		name   string
		result Result
		want   bool
	}{
		{"no suppressions", makeResult("a", Error, "a.java", 1, nil), false},
		{"status absent", suppressed("a", "id", "", "why"), true},
		{"accepted", suppressed("a", "id", Accepted, "why"), true},
		{"under review", suppressed("a", "id", UnderReview, "why"), true},
		{"rejected", suppressed("a", "id", Rejected, "why"), false},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if got := IsSuppressed(&tc.result); got != tc.want {
				t.Errorf("got %v, want %v", got, tc.want)
			}
		})
	}
}

func TestIsSuppressedUnknownStatusDoesNotHide(t *testing.T) {
	r := suppressed("a", "id", Status("somethingElse"), "why")
	if IsSuppressed(&r) {
		t.Error("an unrecognised status must not hide a finding")
	}
}

func TestIsSuppressedAnyAcceptingEntryWins(t *testing.T) {
	r := suppressed("a", "id", Rejected, "denied")
	r.Suppressions = append(r.Suppressions, Suppression{
		Kind:   External,
		Status: statusPtr(Accepted),
	})
	if !IsSuppressed(&r) {
		t.Error("a result with one accepted suppression is suppressed")
	}
}

func TestAcceptWritesAcceptedStatus(t *testing.T) {
	r := makeResult("a", Error, "a.java", 1, fp("id", "trace"))
	if err := Accept(&r, "sink is a constant"); err != nil {
		t.Fatalf("accept: %v", err)
	}
	if len(r.Suppressions) != 1 {
		t.Fatalf("got %d suppressions, want 1", len(r.Suppressions))
	}
	s := r.Suppressions[0]
	if s.Kind != External {
		t.Errorf("kind: got %q, want external", s.Kind)
	}
	if s.Status == nil || *s.Status != Accepted {
		t.Errorf("status: got %v, want accepted", s.Status)
	}
	if s.Justification == nil || *s.Justification != "sink is a constant" {
		t.Errorf("justification: got %v", s.Justification)
	}
	if s.GUID == nil || *s.GUID == "" {
		t.Error("a guid must be generated")
	}
	if s.Properties != nil {
		t.Error("no property bag should be written")
	}
	if s.Location != nil {
		t.Error("an external suppression has no location")
	}
}

func TestDeferWritesUnderReviewStatus(t *testing.T) {
	r := makeResult("a", Error, "a.java", 1, fp("id", "trace"))
	if err := Defer(&r, "waiting on OT-412"); err != nil {
		t.Fatalf("defer: %v", err)
	}
	s := r.Suppressions[0]
	if s.Status == nil || *s.Status != UnderReview {
		t.Errorf("status: got %v, want underReview", s.Status)
	}
	if !IsSuppressed(&r) {
		t.Error("a deferred finding is suppressed")
	}
}

func TestAcceptRequiresJustification(t *testing.T) {
	r := makeResult("a", Error, "a.java", 1, nil)
	if err := Accept(&r, "   "); err == nil {
		t.Error("expected an error for a blank justification")
	}
	if len(r.Suppressions) != 0 {
		t.Error("nothing should be written when validation fails")
	}
}

func TestAcceptReplacesAnExistingSuppression(t *testing.T) {
	r := suppressed("a", "id", UnderReview, "deferred earlier")
	if err := Accept(&r, "now decided: won't fix"); err != nil {
		t.Fatalf("accept: %v", err)
	}
	if len(r.Suppressions) != 1 {
		t.Fatalf("got %d suppressions, want 1", len(r.Suppressions))
	}
	if *r.Suppressions[0].Status != Accepted {
		t.Errorf("status not updated: %v", *r.Suppressions[0].Status)
	}
	if *r.Suppressions[0].Justification != "now decided: won't fix" {
		t.Errorf("justification not updated: %v", *r.Suppressions[0].Justification)
	}
}

func TestUnsuppressRemovesTheEntry(t *testing.T) {
	r := suppressed("a", "id", Accepted, "why")
	if !Unsuppress(&r) {
		t.Error("expected Unsuppress to report a change")
	}
	if len(r.Suppressions) != 0 {
		t.Errorf("got %d suppressions, want 0", len(r.Suppressions))
	}
	if Unsuppress(&r) {
		t.Error("unsuppressing an unsuppressed result should report no change")
	}
}

func TestInheritCopiesSuppressionVerbatim(t *testing.T) {
	guid := "11111111-2222-3333-4444-555555555555"
	base := suppressed("a", "id-a", Accepted, "admin-only input")
	base.Suppressions[0].GUID = &guid
	baseline := makeReport(base)
	current := makeReport(
		makeResult("a", Error, "a.java", 1, fp("id-a", "trace-id-a")),
		makeResult("b", Error, "b.java", 2, fp("id-b", "trace-id-b")),
	)

	n := InheritSuppressions(current, baseline, SourceSinkFingerprintKey)
	if n != 1 {
		t.Fatalf("inherited %d, want 1", n)
	}

	got := current.Results()[0]
	if len(got.Suppressions) != 1 {
		t.Fatalf("got %d suppressions, want 1", len(got.Suppressions))
	}
	s := got.Suppressions[0]
	if s.GUID == nil || *s.GUID != guid {
		t.Errorf("guid not inherited verbatim: %v", s.GUID)
	}
	if s.Justification == nil || *s.Justification != "admin-only input" {
		t.Errorf("justification not inherited verbatim: %v", s.Justification)
	}
	if s.Status == nil || *s.Status != Accepted {
		t.Errorf("status not inherited verbatim: %v", s.Status)
	}
	if len(current.Results()[1].Suppressions) != 0 {
		t.Error("an unmatched result must not be suppressed")
	}
}

func TestInheritIgnoresBaselineEntriesWithoutSuppressions(t *testing.T) {
	baseline := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))
	current := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))

	if n := InheritSuppressions(current, baseline, SourceSinkFingerprintKey); n != 0 {
		t.Errorf("inherited %d, want 0: presence in a baseline is not acceptance", n)
	}
	if IsSuppressed(current.Results()[0]) {
		t.Error("a plain baseline entry must not suppress")
	}
}

func TestInheritDoesNotOverwriteAnExistingDecision(t *testing.T) {
	baseline := makeReport(suppressed("a", "id-a", Accepted, "old decision"))
	current := makeReport(suppressed("a", "id-a", UnderReview, "decided again just now"))

	if n := InheritSuppressions(current, baseline, SourceSinkFingerprintKey); n != 0 {
		t.Errorf("inherited %d, want 0", n)
	}
	if *current.Results()[0].Suppressions[0].Justification != "decided again just now" {
		t.Error("the result's own suppression was overwritten")
	}
}

func TestInheritSkipsRejectedBaselineEntries(t *testing.T) {
	baseline := makeReport(suppressed("a", "id-a", Rejected, "denied"))
	current := makeReport(makeResult("a", Error, "a.java", 1, fp("id-a", "trace-a")))

	if n := InheritSuppressions(current, baseline, SourceSinkFingerprintKey); n != 0 {
		t.Errorf("inherited %d, want 0", n)
	}
	if IsSuppressed(current.Results()[0]) {
		t.Error("a rejected suppression must not hide a finding")
	}
}

func TestSuppressionStatsBreakdown(t *testing.T) {
	report := makeReport(
		suppressed("a", "id-a", Accepted, "won't fix"),
		suppressed("b", "id-b", Accepted, "won't fix either"),
		suppressed("c", "id-c", UnderReview, "not now"),
		suppressed("d", "id-d", Rejected, "denied"),
		suppressed("e", "id-e", Status("weird"), "?"),
		makeResult("f", Error, "f.java", 6, fp("id-f", "trace-f")),
	)

	stats := CollectSuppressionStats(report)
	if stats.Total != 6 {
		t.Errorf("total: got %d, want 6", stats.Total)
	}
	if stats.Suppressed != 3 {
		t.Errorf("suppressed: got %d, want 3", stats.Suppressed)
	}
	if stats.WontFix != 2 {
		t.Errorf("won't fix: got %d, want 2", stats.WontFix)
	}
	if stats.Deferred != 1 {
		t.Errorf("deferred: got %d, want 1", stats.Deferred)
	}
	if stats.NotHonored != 2 {
		t.Errorf("not honored: got %d, want 2 (rejected + unknown status)", stats.NotHonored)
	}
}

func TestJustificationOfReturnsTheHonoredEntry(t *testing.T) {
	r := suppressed("a", "id", Rejected, "denied")
	r.Suppressions = append(r.Suppressions, Suppression{
		Kind:          External,
		Status:        statusPtr(Accepted),
		Justification: strptr("the real reason"),
	})
	got := JustificationOf(&r)
	if !strings.Contains(got, "the real reason") {
		t.Errorf("got %q, want the honored entry's justification", got)
	}
}
