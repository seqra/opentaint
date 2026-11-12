package load_trace

import (
	"os"
	"path/filepath"
	"testing"
)

func TestIssueDetails(t *testing.T) {
	tests := []struct {
		name, message, want string
	}{
		{
			name:    "analyzer template",
			message: "Fix this Semgrep rule and rerun rule loading. Impact: Processing of this rule stopped. Details: Pattern could not be parsed into a valid AST:\nline 1:4 no viable alternative at input 'foo('.",
			want:    "Pattern could not be parsed into a valid AST:\nline 1:4 no viable alternative at input 'foo('",
		},
		{
			name:    "YAML snippet",
			message: "Fix this Semgrep rule and rerun rule loading. Impact: Processing of this rule stopped. Details: while parsing a flow node\n at line 4, column 1:\n    \n    ^\nexpected the node content.",
			want:    "while parsing a flow node\n at line 4, column 1:\n\n    ^\nexpected the node content",
		},
		{
			name:    "no template",
			message: "Something went wrong",
			want:    "Something went wrong",
		},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			if got := issueDetails(tc.message); got != tc.want {
				t.Errorf("issueDetails() = %q, want %q", got, tc.want)
			}
		})
	}
}

func TestRulesFilePath(t *testing.T) {
	root := t.TempDir()
	rulesDir := filepath.Join(root, "rules")
	rulesFile := filepath.Join(root, "single.yaml")
	if err := os.MkdirAll(filepath.Join(rulesDir, "java"), 0o755); err != nil {
		t.Fatal(err)
	}
	for _, path := range []string{filepath.Join(rulesDir, "java", "a.yaml"), rulesFile} {
		if err := os.WriteFile(path, []byte("rules: []\n"), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	rulesets := []string{rulesDir, rulesFile}

	if got, want := rulesFilePath("java/a.yaml", nil, rulesets), filepath.Join(rulesDir, "java", "a.yaml"); got != want {
		t.Errorf("file in a ruleset directory: got %s, want %s", got, want)
	}
	if got := rulesFilePath("", nil, rulesets); got != rulesFile {
		t.Errorf("ruleset that is a file: got %s, want %s", got, rulesFile)
	}
	if got := rulesFilePath("java/missing.yaml", nil, rulesets); got != "java/missing.yaml" {
		t.Errorf("unknown file: got %s, want the name from the trace", got)
	}
}

func TestRulesFilePathFindsTheRuleAmongSameNames(t *testing.T) {
	root := t.TempDir()
	write := func(path, ruleID string) string {
		t.Helper()
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte("rules:\n  - id: "+ruleID+"\n"), 0o644); err != nil {
			t.Fatal(err)
		}
		return path
	}
	fileA := write(filepath.Join(root, "a.yaml"), "rule-a")
	fileB := write(filepath.Join(root, "b.yaml"), "rule-b")
	builtin := filepath.Join(root, "builtin")
	write(filepath.Join(builtin, "go", "ssti.yaml"), "ssti")
	custom := filepath.Join(root, "custom")
	customSSTI := write(filepath.Join(custom, "go", "ssti.yaml"), "my-ssti")

	if got := rulesFilePath("", []string{"rule-b"}, []string{fileA, fileB}); got != fileB {
		t.Errorf("two single-file rulesets: got %s, want %s", got, fileB)
	}
	if got := rulesFilePath("go/ssti.yaml", []string{"my-ssti"}, []string{builtin, custom}); got != customSSTI {
		t.Errorf("one name in two rulesets: got %s, want %s", got, customSSTI)
	}
	if got := rulesFilePath("", nil, []string{fileA, fileB}); got != fileA {
		t.Errorf("no rule IDs: got %s, want the first candidate %s", got, fileA)
	}
}

func TestCollectRuleLoadIssues(t *testing.T) {
	blocking := func(category Category) TraceEntry {
		return TraceEntry{Type: "Error", Message: "Details: problem.", Category: category, Severity: SeverityBlocking}
	}
	nonBlocking := func(category Category) TraceEntry {
		return TraceEntry{Type: "Error", Message: "Details: note.", Category: category, Severity: SeverityNonBlocking}
	}
	trace := &SemgrepLoadTrace{FileTraces: []SemgrepFileLoadTrace{
		{Path: "broken.yaml", Entries: []TraceEntry{blocking(CategoryRuleIssue)}},
		{
			Path:    "bad.yaml",
			Entries: []TraceEntry{nonBlocking(CategoryRuleIssue), {Type: "Info", Message: "Found 3 supported rules"}},
			RuleTraces: []*SemgrepRuleLoadTrace{
				{RuleId: "bad.yaml:syntax", RuleIdInFile: "syntax", Steps: []*SemgrepRuleLoadStepTrace{
					{Entries: []TraceEntry{blocking(CategoryRuleIssue), nonBlocking(CategoryInternalWarning)}},
				}},
				{RuleId: "bad.yaml:regex", RuleIdInFile: "regex", Entries: []TraceEntry{blocking(CategoryUnsupported)}},
				{RuleId: "bad.yaml:good", RuleIdInFile: "good"},
			},
		},
		{Path: "clean.yaml", Entries: []TraceEntry{nonBlocking(CategoryInternalWarning)}},
	}}

	issues := CollectRuleLoadIssues(trace, nil)
	if len(issues.files) != 2 {
		t.Fatalf("files with issues = %d, want 2 (clean.yaml has only an internal note)", len(issues.files))
	}
	if rules := issues.files[1].rules; len(rules) != 2 || rules[0].id != "syntax" || rules[1].id != "regex" {
		t.Errorf("rules with issues = %+v, want syntax and regex", rules)
	}
	if got, want := issues.total(), "1 file and 2 rules skipped, 1 warning"; got != want {
		t.Errorf("total() = %q, want %q", got, want)
	}
	if !CollectRuleLoadIssues(&SemgrepLoadTrace{}, nil).Empty() {
		t.Error("an empty trace should have no issues")
	}
}
