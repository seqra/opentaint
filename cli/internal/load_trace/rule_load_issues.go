package load_trace

import (
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"strings"

	"github.com/seqra/opentaint/internal/output"
	"gopkg.in/yaml.v2"
)

// issueKind is what a rule load problem means for the rules.
type issueKind int

const (
	// issueError stops the rule, or the whole file at the file level: the rule is wrong.
	issueError issueKind = iota
	// issueUnsupported stops the rule: the rule uses a feature that the analyzer lacks.
	issueUnsupported
	// issueInternal stops the rule because of a fault in the analyzer.
	issueInternal
	// issueWarning lets the rule load, possibly without a part of it.
	issueWarning
)

type ruleLoadIssue struct {
	kind    issueKind
	message string
}

type ruleIssues struct {
	id     string
	issues []ruleLoadIssue
}

type fileIssues struct {
	path   string
	issues []ruleLoadIssue
	rules  []ruleIssues
}

// RuleLoadIssues is what the analyzer reported while it loaded the rules, by rules file and rule.
type RuleLoadIssues struct {
	files []fileIssues
}

// Empty reports whether the analyzer loaded every rule without a problem.
func (r RuleLoadIssues) Empty() bool { return len(r.files) == 0 }

func (r RuleLoadIssues) each(visit func(ruleLoadIssue)) {
	for _, file := range r.files {
		for _, issue := range file.issues {
			visit(issue)
		}
		for _, rule := range file.rules {
			for _, issue := range rule.issues {
				visit(issue)
			}
		}
	}
}

// CollectRuleLoadIssues picks the problems out of a rule load trace. The trace names a rules
// file relative to the ruleset that holds it, and rulesetPaths turn that name back into a path.
func CollectRuleLoadIssues(trace *SemgrepLoadTrace, rulesetPaths []string) RuleLoadIssues {
	var result RuleLoadIssues
	for _, fileTrace := range trace.FileTraces {
		file := fileIssues{
			path:   rulesFilePath(fileTrace.Path, ruleIDsIn(fileTrace), rulesetPaths),
			issues: issuesIn(fileTrace.Entries),
		}
		for _, ruleTrace := range fileTrace.RuleTraces {
			if ruleTrace == nil {
				continue
			}
			rule := ruleIssues{id: ruleTrace.RuleIdInFile, issues: issuesIn(ruleTrace.Entries)}
			if rule.id == "" {
				rule.id = ruleTrace.RuleId
			}
			for _, step := range ruleTrace.Steps {
				if step != nil {
					rule.issues = append(rule.issues, issuesIn(step.Entries)...)
				}
			}
			if len(rule.issues) > 0 {
				file.rules = append(file.rules, rule)
			}
		}
		if len(file.issues) > 0 || len(file.rules) > 0 {
			result.files = append(result.files, file)
		}
	}
	return result
}

// rulesFilePath returns the path of a rules file that the trace names relative to its ruleset.
// A ruleset that is a single file has an empty name in the trace. When several rulesets hold a
// file with that name, the file that declares one of ruleIDs is taken, and else the first.
func rulesFilePath(name string, ruleIDs []string, rulesetPaths []string) string {
	var candidates []string
	for _, root := range rulesetPaths {
		info, err := os.Stat(root)
		if err != nil {
			continue
		}
		if !info.IsDir() {
			if name == "" {
				candidates = append(candidates, root)
			}
			continue
		}
		if name == "" {
			continue
		}
		if candidate := filepath.Join(root, filepath.FromSlash(name)); fileExists(candidate) {
			candidates = append(candidates, candidate)
		}
	}
	if len(candidates) == 0 {
		return name
	}
	if len(candidates) > 1 {
		for _, candidate := range candidates {
			if declaresAnyRule(candidate, ruleIDs) {
				return candidate
			}
		}
	}
	return candidates[0]
}

// ruleIDsIn returns the IDs of the rules in a file trace, as the rules file writes them.
func ruleIDsIn(fileTrace SemgrepFileLoadTrace) []string {
	var ids []string
	for _, ruleTrace := range fileTrace.RuleTraces {
		if ruleTrace != nil && ruleTrace.RuleIdInFile != "" {
			ids = append(ids, ruleTrace.RuleIdInFile)
		}
	}
	return ids
}

// declaresAnyRule reports whether the rules file at path declares a rule with one of ids.
func declaresAnyRule(path string, ids []string) bool {
	if len(ids) == 0 {
		return false
	}
	content, err := os.ReadFile(path)
	if err != nil {
		return false
	}
	var rulesFile struct {
		Rules []struct {
			ID string `yaml:"id"`
		} `yaml:"rules"`
	}
	if yaml.Unmarshal(content, &rulesFile) != nil {
		return false
	}
	for _, rule := range rulesFile.Rules {
		if slices.Contains(ids, rule.ID) {
			return true
		}
	}
	return false
}

func fileExists(path string) bool {
	info, err := os.Stat(path)
	return err == nil && !info.IsDir()
}

func issuesIn(entries []TraceEntry) []ruleLoadIssue {
	var issues []ruleLoadIssue
	for _, entry := range entries {
		kind, ok := kindOf(entry)
		if !ok {
			continue
		}
		issues = append(issues, ruleLoadIssue{kind: kind, message: issueDetails(entry.Message)})
	}
	return issues
}

// kindOf classifies a trace entry. Info entries and the internal warnings that need no action
// are not problems.
func kindOf(entry TraceEntry) (issueKind, bool) {
	blocking := entry.Severity == SeverityBlocking
	switch entry.Category {
	case CategoryRuleIssue:
		if blocking {
			return issueError, true
		}
		return issueWarning, true
	case CategoryUnsupported:
		if blocking {
			return issueUnsupported, true
		}
		return issueWarning, true
	case CategoryInternalWarning:
		if blocking {
			return issueInternal, true
		}
	}
	return 0, false
}

// issueDetails keeps the cause from an analyzer message. The analyzer writes every message as
// "<action> Impact: <impact> Details: <cause>.", and the action and the impact follow from the
// category and the severity, which the output already shows. The cause is shown as the
// analyzer wrote it.
func issueDetails(message string) string {
	if _, details, found := strings.Cut(message, " Details: "); found {
		message = strings.TrimSuffix(details, ".")
	}
	lines := strings.Split(message, "\n")
	for i, line := range lines {
		lines[i] = strings.TrimRight(line, " \t")
	}
	return strings.Join(lines, "\n")
}

// Print prints the problems in one block, or says that there are none.
func (r RuleLoadIssues) Print(out *output.Printer) {
	sb := out.Section("Rule Loading")
	if r.Empty() {
		sb.Text("No issues found")
	}
	for _, file := range r.files {
		items := issueItems(out, file.issues)
		for _, rule := range file.rules {
			items = append(items, out.GroupItem(rule.id, issueItems(out, rule.issues)...))
		}
		sb.Group(file.path, items...)
	}
	if !r.Empty() {
		sb.Field("Total", r.total())
	}
	sb.Render()
	out.Blank()
}

func issueItems(out *output.Printer, issues []ruleLoadIssue) []any {
	th := out.Theme()
	items := make([]any, 0, len(issues))
	for _, issue := range issues {
		var label string
		switch issue.kind {
		case issueError:
			label = th.Error.Render("Error:")
		case issueUnsupported:
			label = th.Error.Render("Unsupported:")
		case issueInternal:
			label = th.Error.Render("Internal error:")
		default:
			label = th.Warning.Render("Warning:")
		}
		items = append(items, label+" "+issue.message)
	}
	return items
}

// total counts the rules files and the rules that the problems stopped, and the warnings.
func (r RuleLoadIssues) total() string {
	var skippedFiles, skippedRules, warnings int
	for _, file := range r.files {
		if anyBlocking(file.issues) {
			skippedFiles++
		}
		for _, rule := range file.rules {
			if anyBlocking(rule.issues) {
				skippedRules++
			}
		}
	}
	r.each(func(issue ruleLoadIssue) {
		if issue.kind == issueWarning {
			warnings++
		}
	})

	var skipped []string
	if skippedFiles > 0 {
		skipped = append(skipped, plural(skippedFiles, "file"))
	}
	if skippedRules > 0 {
		skipped = append(skipped, plural(skippedRules, "rule"))
	}
	var parts []string
	if len(skipped) > 0 {
		parts = append(parts, strings.Join(skipped, " and ")+" skipped")
	}
	if warnings > 0 {
		parts = append(parts, plural(warnings, "warning"))
	}
	return strings.Join(parts, ", ")
}

func anyBlocking(issues []ruleLoadIssue) bool {
	for _, issue := range issues {
		if issue.kind != issueWarning {
			return true
		}
	}
	return false
}

func plural(n int, noun string) string {
	if n == 1 {
		return fmt.Sprintf("1 %s", noun)
	}
	return fmt.Sprintf("%d %ss", n, noun)
}
