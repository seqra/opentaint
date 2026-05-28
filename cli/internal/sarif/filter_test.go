package sarif

import "testing"

func TestMatchPath(t *testing.T) {
	r := makeResult("r", Error, "src/main/java/A.java", 10, nil)
	if !matchPath(&r, []string{"src/main/**"}) {
		t.Error("expected src/main/** to match")
	}
	if matchPath(&r, []string{"src/test/**"}) {
		t.Error("expected src/test/** not to match")
	}
	noLoc := Result{}
	if matchPath(&noLoc, []string{"**"}) {
		t.Error("expected no-location result not to match")
	}
	nilPhys := Result{Locations: []Location{{}}}
	if matchPath(&nilPhys, []string{"**"}) {
		t.Error("expected result with nil PhysicalLocation not to match")
	}
}

func TestMatchSeverity(t *testing.T) {
	r := makeResult("r", Error, "a.java", 1, nil)
	if !matchSeverity(&r, []string{"ERROR"}) {
		t.Error("expected case-insensitive error match")
	}
	if matchSeverity(&r, []string{"warning"}) {
		t.Error("expected warning not to match an error")
	}
	nilLevel := Result{Locations: r.Locations}
	if !matchSeverity(&nilLevel, []string{"note"}) {
		t.Error("expected nil level to be treated as note")
	}
}

func TestMatchFingerprint(t *testing.T) {
	r := makeResult("r", Error, "a.java", 1, map[string]string{
		DefaultFingerprintKey: "abc123def456",
	})
	if !matchFingerprint(&r, "", []string{"abc123"}) {
		t.Error("expected git-style prefix match on default key")
	}
	if matchFingerprint(&r, "", []string{"zzz"}) {
		t.Error("expected non-prefix not to match")
	}
	if matchFingerprint(&r, "missing/key", []string{"abc"}) {
		t.Error("expected absent key not to match")
	}
}

func TestFilterCombinesAndOr(t *testing.T) {
	a := makeResult("rules:sqli", Error, "src/A.java", 1, nil)
	b := makeResult("rules:xss", Warning, "src/B.java", 2, nil)
	c := makeResult("rules:sqli", Warning, "test/C.java", 3, nil)
	report := makeReport(a, b, c)

	// (error OR warning) AND path src/** -> A and B, not C.
	got := report.Filter(Filters{
		Severities: []string{"error", "warning"},
		Paths:      []string{"src/**"},
	})
	if n := len(got.Runs[0].Results); n != 2 {
		t.Fatalf("expected 2 results, got %d", n)
	}
}

func TestFilterInactiveReturnsSameReport(t *testing.T) {
	report := makeReport(makeResult("r", Error, "a.java", 1, nil))
	if report.Filter(Filters{}) != report {
		t.Error("inactive filter should return the original report pointer")
	}
}

func TestValidateSeverity(t *testing.T) {
	for _, ok := range []string{"error", "WARNING", " note ", "none"} {
		if err := ValidateSeverity(ok); err != nil {
			t.Errorf("expected %q valid: %v", ok, err)
		}
	}
	if ValidateSeverity("critical") == nil {
		t.Error("expected 'critical' to be invalid")
	}
}

func TestRuleLeaf(t *testing.T) {
	cases := map[string]string{
		"rules/java/security:sql-injection-in-spring-app": "sql-injection-in-spring-app", // raw, first ':'
		"rules.java.sql-injection-in-spring-app":          "sql-injection-in-spring-app", // dotted, last '.'
		"bare-rule":                                       "bare-rule",                   // neither
		"a.b:c":                                          "c",                            // both separators; colon wins
		":leaf":                                          "leaf",                         // leading colon
		"a.":                                             "",                             // trailing dot -> empty leaf
		"":                                               "",                             // empty id
	}
	for in, want := range cases {
		if got := ruleLeaf(in); got != want {
			t.Errorf("ruleLeaf(%q) = %q, want %q", in, got, want)
		}
	}
}

func TestMatchRuleID(t *testing.T) {
	full := "rules/java/security:sql-injection-in-spring-app"
	r := makeResult(full, Error, "a.java", 1, nil)

	if !matchRuleID(&r, []string{full}) {
		t.Error("expected full id to match")
	}
	if !matchRuleID(&r, []string{"sql-injection-in-spring-app"}) {
		t.Error("expected leaf to match")
	}
	if !matchRuleID(&r, []string{"rules/java/**"}) {
		t.Error("expected doublestar glob over full id to match")
	}
	if matchRuleID(&r, []string{"other-rule"}) {
		t.Error("expected unrelated value not to match")
	}
	nilRule := Result{}
	if matchRuleID(&nilRule, []string{"**"}) {
		t.Error("expected nil rule id not to match")
	}

	emptyRule := makeResult("", Error, "a.java", 1, nil)
	if matchRuleID(&emptyRule, []string{""}) {
		t.Error("expected empty filter value not to match (guard)")
	}
}

func TestFilterRuleIDDimension(t *testing.T) {
	a := makeResult("rules:sql-injection-in-spring-app", Error, "a.java", 1, nil)
	b := makeResult("rules:xss", Warning, "b.java", 2, nil)
	got := makeReport(a, b).Filter(Filters{RuleIDs: []string{"sql-injection-in-spring-app"}})
	if n := len(got.Runs[0].Results); n != 1 {
		t.Fatalf("expected 1 result, got %d", n)
	}
}
