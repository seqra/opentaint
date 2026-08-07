package sarif

import (
	"strings"
	"testing"
)

func TestResolveIdentityKeyDefaultsToSourceSink(t *testing.T) {
	key, err := ResolveIdentityKey("")
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if key != SourceSinkFingerprintKey {
		t.Errorf("got %q, want %q", key, SourceSinkFingerprintKey)
	}
}

func TestResolveIdentityKeyAcceptsExplicitKey(t *testing.T) {
	key, err := ResolveIdentityKey(TraceFingerprintKey)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if key != TraceFingerprintKey {
		t.Errorf("got %q, want %q", key, TraceFingerprintKey)
	}
}

func TestResolveIdentityKeyRejectsBlank(t *testing.T) {
	if _, err := ResolveIdentityKey("   "); err == nil {
		t.Error("expected error for whitespace-only key")
	}
}

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
		makeResult("a", Error, "a.java", 1, map[string]string{SourceSinkFingerprintKey: "q3Vf9k2nAAA"}),
		makeResult("b", Error, "b.java", 2, map[string]string{SourceSinkFingerprintKey: "8bc1d2xxBBB"}),
	)
	r, err := ResolvePrefix(report, SourceSinkFingerprintKey, "q3Vf9k")
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if *r.RuleID != "a" {
		t.Errorf("resolved to rule %q, want a", *r.RuleID)
	}
}

func TestResolvePrefixExactValueMatches(t *testing.T) {
	report := makeReport(
		makeResult("a", Error, "a.java", 1, map[string]string{SourceSinkFingerprintKey: "q3Vf9k2nAAA"}),
	)
	if _, err := ResolvePrefix(report, SourceSinkFingerprintKey, "q3Vf9k2nAAA"); err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestResolvePrefixAmbiguousIsAnError(t *testing.T) {
	report := makeReport(
		makeResult("a", Error, "a.java", 1, map[string]string{SourceSinkFingerprintKey: "q3Vf9kAAA"}),
		makeResult("b", Error, "b.java", 2, map[string]string{SourceSinkFingerprintKey: "q3Vf9kBBB"}),
	)
	_, err := ResolvePrefix(report, SourceSinkFingerprintKey, "q3Vf9k")
	if err == nil {
		t.Fatal("expected ambiguous prefix to error")
	}
	if !strings.Contains(err.Error(), "q3Vf9kAAA") || !strings.Contains(err.Error(), "q3Vf9kBBB") {
		t.Errorf("error should list the candidates, got: %v", err)
	}
}

func TestResolvePrefixNoMatchIsAnError(t *testing.T) {
	report := makeReport(
		makeResult("a", Error, "a.java", 1, map[string]string{SourceSinkFingerprintKey: "q3Vf9kAAA"}),
	)
	if _, err := ResolvePrefix(report, SourceSinkFingerprintKey, "zzzz"); err == nil {
		t.Error("expected unmatched prefix to error")
	}
}

func TestResolvePrefixEmptyIsAnError(t *testing.T) {
	report := makeReport(
		makeResult("a", Error, "a.java", 1, map[string]string{SourceSinkFingerprintKey: "q3Vf9kAAA"}),
	)
	if _, err := ResolvePrefix(report, SourceSinkFingerprintKey, ""); err == nil {
		t.Error("expected empty prefix to error rather than match everything")
	}
}

func TestResolveIdentityKeyExpandsAliases(t *testing.T) {
	cases := map[string]string{
		"sink":          SinkFingerprintKey,
		"SINK":          SinkFingerprintKey,
		" source-sink ": SourceSinkFingerprintKey,
		"sourcesink":    SourceSinkFingerprintKey,
		"trace":         TraceFingerprintKey,
	}
	for in, want := range cases {
		got, err := ResolveIdentityKey(in)
		if err != nil {
			t.Fatalf("ResolveIdentityKey(%q): %v", in, err)
		}
		if got != want {
			t.Errorf("ResolveIdentityKey(%q) = %q, want %q", in, got, want)
		}
	}
}

func TestResolveIdentityKeyPassesUnknownKeysThrough(t *testing.T) {
	got, err := ResolveIdentityKey("somethingElse/v9")
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if got != "somethingElse/v9" {
		t.Errorf("got %q, want the key unchanged", got)
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

	cmp, err := CompareToBaseline(current, baseline, SinkFingerprintKey)
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
