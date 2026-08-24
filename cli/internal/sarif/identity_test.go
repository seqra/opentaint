package sarif

import (
	"strings"
	"testing"
)

func TestIdentityReadsChosenKey(t *testing.T) {
	r := makeResult("rule", Error, "a.java", 1, map[string]string{
		SourceSinkFingerprintKey: "src-sink-hash",
		TraceFingerprintKey:      "trace-hash",
	})
	got, ok := Identity(&r, SourceSinkFingerprintKey)
	if !ok || got != "src-sink-hash" {
		t.Errorf("got (%q, %v), want (src-sink-hash, true)", got, ok)
	}
	got, ok = Identity(&r, TraceFingerprintKey)
	if !ok || got != "trace-hash" {
		t.Errorf("got (%q, %v), want (trace-hash, true)", got, ok)
	}
}

func TestIdentityMissingKeyIsNotIdentifiable(t *testing.T) {
	r := makeResult("rule", Error, "a.java", 1, map[string]string{TraceFingerprintKey: "trace"})
	if _, ok := Identity(&r, SourceSinkFingerprintKey); ok {
		t.Error("expected missing key to report not-identifiable")
	}

	noPrints := makeResult("rule", Error, "a.java", 1, nil)
	if _, ok := Identity(&noPrints, SourceSinkFingerprintKey); ok {
		t.Error("expected nil partialFingerprints to report not-identifiable")
	}
}

func TestResultsIteratesEveryRun(t *testing.T) {
	report := &Report{Runs: []Run{
		{Results: []Result{makeResult("a", Error, "a.java", 1, nil)}},
		{Results: []Result{makeResult("b", Error, "b.java", 2, nil), makeResult("c", Error, "c.java", 3, nil)}},
	}}
	got := report.Results()
	if len(got) != 3 {
		t.Fatalf("got %d results, want 3", len(got))
	}
	// Results must be pointers into the report so mutations stick.
	got[0].Level = lvlptr(Note)
	if *report.Runs[0].Results[0].Level != Note {
		t.Error("Results() did not return pointers into the report")
	}
}

func TestResolvePrefixFindsUniqueMatch(t *testing.T) {
	report := makeReport(
		makeResult("a", Error, "a.java", 1, map[string]string{SinkFingerprintKey: "q3Vf9k2nAAA"}),
		makeResult("b", Error, "b.java", 2, map[string]string{SinkFingerprintKey: "8bc1d2xxBBB"}),
	)
	matched, err := ResolvePrefix(report, "q3Vf9k")
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(matched) != 1 || *matched[0].RuleID != "a" {
		t.Errorf("resolved %d results, want the one with rule a", len(matched))
	}
}

// Two results sharing one identity value are the same finding to a decision,
// so an exact or prefix match on that value resolves to both rather than
// erroring as ambiguous — under the sink identity such duplicates are
// legitimate, and no longer prefix could ever separate them.
func TestResolvePrefixReturnsAllDuplicatesOfOneIdentity(t *testing.T) {
	report := makeReport(
		makeResult("a", Error, "a.java", 1, map[string]string{SinkFingerprintKey: "q3Vf9kSAME"}),
		makeResult("a", Error, "a.java", 9, map[string]string{SinkFingerprintKey: "q3Vf9kSAME"}),
	)
	matched, err := ResolvePrefix(report, "q3Vf9kSAME")
	if err != nil {
		t.Fatalf("duplicates of one identity must resolve, got: %v", err)
	}
	if len(matched) != 2 {
		t.Errorf("got %d results, want both duplicates", len(matched))
	}
}

func TestResolvePrefixExactValueMatches(t *testing.T) {
	report := makeReport(
		makeResult("a", Error, "a.java", 1, map[string]string{SinkFingerprintKey: "q3Vf9k2nAAA"}),
	)
	if _, err := ResolvePrefix(report, "q3Vf9k2nAAA"); err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestResolvePrefixAmbiguousIsAnError(t *testing.T) {
	report := makeReport(
		makeResult("a", Error, "a.java", 1, map[string]string{SinkFingerprintKey: "q3Vf9kAAA"}),
		makeResult("b", Error, "b.java", 2, map[string]string{SinkFingerprintKey: "q3Vf9kBBB"}),
	)
	_, err := ResolvePrefix(report, "q3Vf9k")
	if err == nil {
		t.Fatal("expected ambiguous prefix to error")
	}
	if !strings.Contains(err.Error(), "q3Vf9kAAA") || !strings.Contains(err.Error(), "q3Vf9kBBB") {
		t.Errorf("error should list the candidates, got: %v", err)
	}
}

func TestResolvePrefixNoMatchIsAnError(t *testing.T) {
	report := makeReport(
		makeResult("a", Error, "a.java", 1, map[string]string{SinkFingerprintKey: "q3Vf9kAAA"}),
	)
	if _, err := ResolvePrefix(report, "zzzz"); err == nil {
		t.Error("expected unmatched prefix to error")
	}
}

func TestResolvePrefixEmptyIsAnError(t *testing.T) {
	report := makeReport(
		makeResult("a", Error, "a.java", 1, map[string]string{SinkFingerprintKey: "q3Vf9kAAA"}),
	)
	if _, err := ResolvePrefix(report, ""); err == nil {
		t.Error("expected empty prefix to error rather than match everything")
	}
}

// The analyzer hashes the rule id into every fingerprint, so two rules on one
// statement carry different sink hashes and must not be conflated.
func TestCompareOnSinkHashSeparatesRulesOnOneStatement(t *testing.T) {
	sink := func(v string) map[string]string { return map[string]string{SinkFingerprintKey: v} }
	baseline := makeReport(makeResult("sqli", Error, "a.java", 1, sink("sqli-s1")))
	current := makeReport(
		makeResult("sqli", Error, "a.java", 1, sink("sqli-s1")), // unchanged
		makeResult("xss", Error, "a.java", 1, sink("xss-s1")),   // new: different rule
	)

	cmp, err := CompareToBaseline(current, baseline)
	if err != nil {
		t.Fatalf("compare: %v", err)
	}
	results := current.Results()
	if got := cmp.StateOf(results[0]); got != Unchanged {
		t.Errorf("same rule and sink: got %q, want unchanged", got)
	}
	if got := cmp.StateOf(results[1]); got != New {
		t.Errorf("other rule on the same sink: got %q, want new", got)
	}
	if len(cmp.Absent) != 0 {
		t.Errorf("nothing was fixed, but %d results are absent", len(cmp.Absent))
	}
}
