package rules

import (
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"
)

// ruleset writes a ruleset tree and returns its root.
func ruleset(t *testing.T, files map[string]string) string {
	t.Helper()
	root := t.TempDir()
	for name, content := range files {
		path := filepath.Join(root, filepath.FromSlash(name))
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	return root
}

func TestListRuleIDs(t *testing.T) {
	root := ruleset(t, map[string]string{
		"java/security/sqli.yaml": "rules:\n  - id: sql-injection\n  - id: sql-injection-jdbc\n",
		"java/security/xss.yml":   "rules:\n  - id: reflected-xss\n",
		"java/lib/sources.yaml":   "rules:\n  - id: servlet-source\n",
		"README.md":               "not a ruleset file",
	})

	got := ListRuleIDs([]string{root})
	sort.Strings(got)
	want := []string{
		"java/lib/sources.yaml:servlet-source",
		"java/security/sqli.yaml:sql-injection",
		"java/security/sqli.yaml:sql-injection-jdbc",
		"java/security/xss.yml:reflected-xss",
	}
	if strings.Join(got, "\n") != strings.Join(want, "\n") {
		t.Errorf("got:\n%s\nwant:\n%s", strings.Join(got, "\n"), strings.Join(want, "\n"))
	}
}

func TestListRuleIDsSkipsUnparseableFiles(t *testing.T) {
	root := ruleset(t, map[string]string{
		"good.yaml": "rules:\n  - id: good-rule\n",
		"bad.yaml":  "this: [is: not: valid: yaml",
	})
	got := ListRuleIDs([]string{root})
	if len(got) != 1 || got[0] != "good.yaml:good-rule" {
		t.Errorf("got %v, want just the parseable rule", got)
	}
}

func TestListRuleIDsMergesRoots(t *testing.T) {
	a := ruleset(t, map[string]string{"a.yaml": "rules:\n  - id: rule-a\n"})
	b := ruleset(t, map[string]string{"b.yaml": "rules:\n  - id: rule-b\n"})
	got := ListRuleIDs([]string{a, b})
	sort.Strings(got)
	if len(got) != 2 || got[0] != "a.yaml:rule-a" || got[1] != "b.yaml:rule-b" {
		t.Errorf("got %v", got)
	}
}

func TestMatchesAnyUsesTheSummaryRuleIDGrammar(t *testing.T) {
	const id = "java/security/sqli.yaml:sql-injection"
	cases := []struct {
		pattern string
		want    bool
	}{
		{"java/security/sqli.yaml:sql-injection", true}, // full id
		{"sql-injection", true},                         // exact leaf
		{"java/security/**", true},                      // glob over the full id
		{"java/**/sqli.yaml:*", true},
		{"sql-*", false}, // globs match the FULL id only, same as summary --rule-id
		{"sql-injection-jdbc", false},
		{"go/**", false},
		{"", false},
	}
	for _, tc := range cases {
		if got := matchesAny(id, []string{tc.pattern}); got != tc.want {
			t.Errorf("matchesAny(%q, [%q]) = %v, want %v", id, tc.pattern, got, tc.want)
		}
	}
}

func TestSelectWithNeitherListReturnsNothing(t *testing.T) {
	root := ruleset(t, map[string]string{"a.yaml": "rules:\n  - id: rule-a\n"})
	got, err := Select(Selection{}, []string{root})
	if err != nil {
		t.Fatalf("select: %v", err)
	}
	if got != nil {
		t.Errorf("got %v, want nil: with no lists the analyzer runs every rule", got)
	}
}

func TestSelectOnly(t *testing.T) {
	root := ruleset(t, map[string]string{
		"a.yaml": "rules:\n  - id: keep-me\n  - id: drop-me\n",
	})
	got, err := Select(Selection{Only: []string{"keep-me"}}, []string{root})
	if err != nil {
		t.Fatalf("select: %v", err)
	}
	if len(got) != 1 || got[0] != "a.yaml:keep-me" {
		t.Errorf("got %v", got)
	}
}

func TestSelectExclude(t *testing.T) {
	root := ruleset(t, map[string]string{
		"a.yaml": "rules:\n  - id: keep-me\n  - id: drop-me\n",
	})
	got, err := Select(Selection{Exclude: []string{"drop-me"}}, []string{root})
	if err != nil {
		t.Fatalf("select: %v", err)
	}
	if len(got) != 1 || got[0] != "a.yaml:keep-me" {
		t.Errorf("got %v", got)
	}
}

func TestSelectExcludeAppliesAfterOnly(t *testing.T) {
	root := ruleset(t, map[string]string{
		"a.yaml": "rules:\n  - id: sqli-one\n  - id: sqli-two\n  - id: xss\n",
	})
	got, err := Select(Selection{Only: []string{"a.yaml:sqli-*"}, Exclude: []string{"sqli-two"}}, []string{root})
	if err != nil {
		t.Fatalf("select: %v", err)
	}
	if len(got) != 1 || got[0] != "a.yaml:sqli-one" {
		t.Errorf("got %v", got)
	}
}

func TestSelectPullsInReferencedRules(t *testing.T) {
	root := ruleset(t, map[string]string{
		"security/sqli.yaml": "rules:\n  - id: sql-injection\n    join:\n      refs:\n        - rule: lib/sources.yaml#servlet-source\n",
		"lib/sources.yaml":   "rules:\n  - id: servlet-source\n",
	})
	got, err := Select(Selection{Only: []string{"sql-injection"}}, []string{root})
	if err != nil {
		t.Fatalf("select: %v", err)
	}
	sort.Strings(got)
	if len(got) != 2 || got[1] != "security/sqli.yaml:sql-injection" || got[0] != "lib/sources.yaml:servlet-source" {
		t.Errorf("got %v, want the rule plus the library rule it joins", got)
	}
}

func TestSelectReAddsAnExcludedRuleThatSurvivorsNeed(t *testing.T) {
	// Excluding a library rule that a kept rule joins against would produce a
	// rule that cannot match anything. Reference expansion brings it back.
	root := ruleset(t, map[string]string{
		"security/sqli.yaml": "rules:\n  - id: sql-injection\n    join:\n      refs:\n        - rule: lib/sources.yaml#servlet-source\n",
		"lib/sources.yaml":   "rules:\n  - id: servlet-source\n",
	})
	got, err := Select(Selection{Exclude: []string{"lib/**"}}, []string{root})
	if err != nil {
		t.Fatalf("select: %v", err)
	}
	if len(got) != 2 {
		t.Errorf("got %v, want the excluded library rule restored", got)
	}
}

func TestSelectEmptyResultIsAnError(t *testing.T) {
	root := ruleset(t, map[string]string{"a.yaml": "rules:\n  - id: rule-a\n"})
	if _, err := Select(Selection{Only: []string{"nothing-matches-this"}}, []string{root}); err == nil {
		t.Error("expected an error rather than a scan with zero rules")
	}
	if _, err := Select(Selection{Exclude: []string{"**"}}, []string{root}); err == nil {
		t.Error("excluding everything should error rather than scan with zero rules")
	}
}

func TestSelectWithNoRulesFoundIsAnError(t *testing.T) {
	if _, err := Select(Selection{Only: []string{"x"}}, []string{t.TempDir()}); err == nil {
		t.Error("expected an error when the ruleset holds no rules at all")
	}
}

func TestApplyExclusionsFiltersAnExplicitList(t *testing.T) {
	ids := []string{"a.yaml:keep-me", "a.yaml:drop-me", "b.yaml:drop-me-too"}
	got, err := ApplyExclusions(ids, []string{"*:drop-*"})
	if err != nil {
		t.Fatalf("apply: %v", err)
	}
	if len(got) != 1 || got[0] != "a.yaml:keep-me" {
		t.Errorf("got %v", got)
	}
}

func TestApplyExclusionsWithNoPatternsIsIdentity(t *testing.T) {
	ids := []string{"a.yaml:x"}
	got, err := ApplyExclusions(ids, nil)
	if err != nil {
		t.Fatalf("apply: %v", err)
	}
	if len(got) != 1 || got[0] != "a.yaml:x" {
		t.Errorf("got %v", got)
	}
}

func TestApplyExclusionsEmptyingTheListIsAnError(t *testing.T) {
	if _, err := ApplyExclusions([]string{"a.yaml:x"}, []string{"**"}); err == nil {
		t.Error("excluding every explicitly requested rule should error, not scan nothing")
	}
}

func TestUnmatchedReportsPatternsThatSelectNothing(t *testing.T) {
	all := []string{"a.yaml:keep-me", "java/security/sqli.yaml:sql-injection"}
	sel := Selection{
		Only:    []string{"keep-me", "no-such-rule"},
		Exclude: []string{"java/**", "typo-*"},
	}
	got := sel.Unmatched(all)
	if len(got) != 2 || got[0] != "no-such-rule" || got[1] != "typo-*" {
		t.Errorf("got %v, want [no-such-rule typo-*]", got)
	}
}

func TestUnmatchedIsEmptyWhenEverythingMatches(t *testing.T) {
	all := []string{"a.yaml:x"}
	if got := (Selection{Exclude: []string{"x"}}).Unmatched(all); got != nil {
		t.Errorf("got %v, want nil", got)
	}
}
