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

// Selection is the allow/deny list of rule ids from the configuration file.
// These control which rules the analyzer runs at all — they are not
// suppressions, and an excluded rule produces nothing to suppress.
type Selection struct {
	Only    []string // if non-empty, only rules matching these run
	Exclude []string // rules matching these never run
}

// Active reports whether the selection restricts anything.
func (s Selection) Active() bool {
	return len(s.Only) > 0 || len(s.Exclude) > 0
}

// ListRuleIDs returns every rule id defined under the given ruleset roots, in
// the "<path relative to the root>.yaml:<id>" form the analyzer matches on.
// Files that cannot be read or parsed are skipped: a malformed rule file is the
// rule loader's problem to report, not a reason to fail rule selection.
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
			for _, r := range rf.Rules {
				if r.ID == "" {
					continue
				}
				ids = append(ids, filepath.ToSlash(relPath)+":"+r.ID)
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

// Resolved is a rule selection lowered to the exact ids the analyzer accepts:
// Include feeds --semgrep-rule-id (empty = run everything), Exclude feeds
// --semgrep-rule-id-exclude. Patterns never reach the analyzer.
type Resolved struct {
	Include []string
	Exclude []string
}

// Select resolves a Selection against the ruleset roots.
//
// An exclusion-only selection resolves to just the excluded ids — excluding
// one rule passes one exclusion arg, not the 150-rule complement. When an
// allow-list is present the inclusion list is unavoidable (the analyzer
// matches exact ids), so exclusions are subtracted from it CLI-side and rules
// referenced by the survivors are pulled back in: a rule whose joined library
// rule was excluded could never match anything, which is a silently broken
// scan rather than a narrower one. On the exclusion side the analyzer itself
// resolves join refs past exclusions, so no such repair is needed.
func Select(selection Selection, roots []string) (Resolved, error) {
	if !selection.Active() {
		return Resolved{}, nil
	}

	all := ListRuleIDs(roots)
	if len(all) == 0 {
		return Resolved{}, fmt.Errorf("rules.only/rules.exclude are configured but no rules were found in the ruleset")
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
		return Resolved{}, fmt.Errorf("rules.only/rules.exclude select no rules at all: nothing would be scanned")
	}

	if len(selection.Only) == 0 {
		sort.Strings(excluded)
		return Resolved{Exclude: excluded}, nil
	}

	expanded := ExpandRuleIDs(kept, roots)
	sort.Strings(expanded)
	return Resolved{Include: expanded}, nil
}

// matchesAny delegates to the one rule-id grammar (sarif.MatchesRuleID), so a
// pattern behaves identically in rules.only/rules.exclude, --exclude-rule-id,
// and summary's --rule-id filter: exact full "path.yaml:id", exact bare name,
// or a doublestar glob over the full id.
func matchesAny(id string, patterns []string) bool {
	return sarif.MatchesRuleID(id, patterns)
}

// ApplyExclusions filters an explicit rule-id list (--rule-id) by exclusion
// patterns (--exclude-rule-id), so the two flags compose instead of one
// silently winning. Emptying the list is an error: every id in it was asked
// for by name, so excluding them all leaves a scan that checks nothing.
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
		return nil, fmt.Errorf("--exclude-rule-id excludes every rule selected by --rule-id: nothing would be scanned")
	}
	return kept, nil
}

// Unmatched returns the selection patterns that match none of the given rule
// ids, in Only-then-Exclude order. A pattern matching nothing is usually a
// typo'd rule name, and silently ignoring it would make an exclusion look
// effective when it never was — the caller should surface these.
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
