package rules

import (
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"github.com/seqra/opentaint/internal/sarif"
	"gopkg.in/yaml.v2"
)

// Selection is the rules that the analyzer runs: rules.only and rules.exclude, or --exclude-rule-id.
type Selection struct {
	Only    []string // if non-empty, only rules matching these run
	Exclude []string // rules matching these never run
}

// Active reports whether the selection restricts anything.
func (s Selection) Active() bool {
	return len(s.Only) > 0 || len(s.Exclude) > 0
}

// ListRuleIDs returns the IDs of the rules under roots as <path>.yaml:<id>. It skips the files that
// it cannot parse: the analyzer reports them.
func ListRuleIDs(roots []string) []string {
	var ids []string
	for _, root := range roots {
		_ = filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
			if err != nil || d.IsDir() || !isRuleFile(path) {
				return nil
			}
			relPath, relErr := filepath.Rel(root, path)
			if relErr != nil {
				return nil
			}
			data, readErr := os.ReadFile(path)
			if readErr != nil {
				return nil
			}
			var rf ruleFile
			if yaml.Unmarshal(data, &rf) != nil {
				return nil
			}
			prefix := filepath.ToSlash(relPath)
			if prefix == "." {
				// The analyzer names a rule in a single-file ruleset ":<id>".
				prefix = ""
			}
			for _, r := range rf.Rules {
				if r.ID == "" {
					continue
				}
				ids = append(ids, prefix+":"+r.ID)
			}
			return nil
		})
	}
	return ids
}

func isRuleFile(path string) bool {
	ext := strings.ToLower(filepath.Ext(path))
	return ext == ".yaml" || ext == ".yml"
}

// Resolved holds the exact IDs for --semgrep-rule-id (Include, empty for all rules) and
// --semgrep-rule-id-exclude (Exclude).
type Resolved struct {
	Include []string
	Exclude []string
}

// Select resolves selection against the rules under roots. Without rules.only it returns only the
// excluded IDs. With rules.only it returns the included IDs plus the library rules they join, so
// that excluding a library rule does not break the rules that use it.
func Select(selection Selection, roots []string) (Resolved, error) {
	if !selection.Active() {
		return Resolved{}, nil
	}

	all := ListRuleIDs(roots)
	if len(all) == 0 {
		return Resolved{}, fmt.Errorf("the ruleset has no rules")
	}

	var kept, excluded []string
	for _, id := range all {
		if len(selection.Only) > 0 && !matchesAny(id, selection.Only) {
			continue
		}
		if matchesAny(id, selection.Exclude) {
			excluded = append(excluded, id)
			continue
		}
		kept = append(kept, id)
	}
	if len(kept) == 0 {
		return Resolved{}, fmt.Errorf("rules.only and rules.exclude leave no rule")
	}

	if len(selection.Only) == 0 {
		sort.Strings(excluded)
		return Resolved{Exclude: excluded}, nil
	}

	expanded := ExpandRuleIDs(kept, roots)
	sort.Strings(expanded)
	return Resolved{Include: expanded}, nil
}

// matchesAny matches id as summary --rule-id does: the full ID, the leaf name, or a glob over the
// full ID. The full ID is <path>.yaml:<id> or, as the SARIF report writes it, the dotted ID.
func matchesAny(id string, patterns []string) bool {
	return sarif.MatchesRuleID(id, patterns) || sarif.MatchesRuleID(dottedRuleID(id), patterns)
}

// dottedRuleID is the rule ID that the analyzer writes in a Semgrep-style SARIF report:
// go/security/cmdi.yaml:command-injection is go.security.command-injection.
func dottedRuleID(id string) string {
	path, name, ok := strings.Cut(id, ":")
	if !ok {
		return id
	}
	parts := strings.Split(path, "/")
	return strings.Join(append(parts[:len(parts)-1], name), ".")
}

// ApplyExclusions removes the IDs that match patterns. It fails when none is left.
func ApplyExclusions(ids, patterns []string) ([]string, error) {
	if len(patterns) == 0 {
		return ids, nil
	}
	var kept []string
	for _, id := range ids {
		if !matchesAny(id, patterns) {
			kept = append(kept, id)
		}
	}
	if len(ids) > 0 && len(kept) == 0 {
		return nil, fmt.Errorf("--exclude-rule-id excludes every --rule-id")
	}
	return kept, nil
}

// Unmatched returns the patterns, rules.only first, that match no ID in all.
func (s Selection) Unmatched(all []string) []string {
	var unmatched []string
	for _, pattern := range append(append([]string{}, s.Only...), s.Exclude...) {
		if pattern == "" {
			continue
		}
		if !anyIDMatches(all, pattern) {
			unmatched = append(unmatched, pattern)
		}
	}
	return unmatched
}

func anyIDMatches(all []string, pattern string) bool {
	for _, id := range all {
		if matchesAny(id, []string{pattern}) {
			return true
		}
	}
	return false
}
