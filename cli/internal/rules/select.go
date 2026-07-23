package rules

import (
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"github.com/bmatcuk/doublestar/v4"
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

// Select resolves a Selection against the ruleset roots and returns the rule ids
// to pass to the analyzer, or nil when the selection restricts nothing (in which
// case the analyzer runs every rule, as it always has).
//
// The analyzer only supports inclusion, so an exclusion list is applied by
// enumerating every rule and subtracting. Rules referenced by the survivors are
// then pulled back in: a rule whose joined library rule was excluded could never
// match anything, which is a silently broken scan rather than a narrower one.
func Select(selection Selection, roots []string) ([]string, error) {
	if !selection.Active() {
		return nil, nil
	}

	all := ListRuleIDs(roots)
	if len(all) == 0 {
		return nil, fmt.Errorf("rules.only/rules.exclude are configured but no rules were found in the ruleset")
	}

	var kept []string
	for _, id := range all {
		if len(selection.Only) > 0 && !matchesAny(id, selection.Only) {
			continue
		}
		if matchesAny(id, selection.Exclude) {
			continue
		}
		kept = append(kept, id)
	}
	if len(kept) == 0 {
		return nil, fmt.Errorf("rules.only/rules.exclude select no rules at all; nothing would be scanned")
	}

	expanded := ExpandRuleIDs(kept, roots)
	sort.Strings(expanded)
	return expanded, nil
}

func matchesAny(id string, patterns []string) bool {
	for _, p := range patterns {
		if matchesPattern(id, p) {
			return true
		}
	}
	return false
}

// matchesPattern matches a rule id as a full "path.yaml:id", as a bare leaf
// name, or as a doublestar glob over either. Globbing the leaf as well as the
// full id is what makes the natural "sqli-*" work; matching only the full id
// would silently select nothing, since the leaf never contains the path.
func matchesPattern(id, pattern string) bool {
	pattern = strings.TrimSpace(pattern)
	if pattern == "" {
		return false
	}
	if id == pattern {
		return true
	}
	if matched, err := doublestar.Match(pattern, id); err == nil && matched {
		return true
	}
	_, leaf, ok := splitRuleID(id)
	if !ok {
		return false
	}
	if leaf == pattern {
		return true
	}
	matched, err := doublestar.Match(pattern, leaf)
	return err == nil && matched
}
