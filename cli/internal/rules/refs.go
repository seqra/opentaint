package rules

import (
	"os"
	"path/filepath"
	"strings"

	"gopkg.in/yaml.v2"
)

// ruleFile is the minimal shape parsed from a ruleset YAML: each rule's id and
// the rules it pulls in via join.refs.
type ruleFile struct {
	Rules []struct {
		ID   string `yaml:"id"`
		Join struct {
			Refs []struct {
				Rule string `yaml:"rule"`
			} `yaml:"refs"`
		} `yaml:"join"`
	} `yaml:"rules"`
}

// ExpandRuleIDs returns ruleIDs together with every rule transitively
// referenced through join.refs, resolved against the given ruleset roots. A
// full rule id is "<path-relative-to-root>:<short-id>"; a ref is the same path
// with '#' instead of ':'. Originals come first, the rest in BFS order;
// duplicates are removed and ids that can't be resolved on disk pass through
// unchanged.
func ExpandRuleIDs(ruleIDs []string, rulesetRoots []string) []string {
	seen := make(map[string]bool, len(ruleIDs))
	var result []string
	queue := append([]string(nil), ruleIDs...)

	for len(queue) > 0 {
		id := queue[0]
		queue = queue[1:]
		if seen[id] {
			continue
		}
		seen[id] = true
		result = append(result, id)

		for _, ref := range refsOf(id, rulesetRoots) {
			if !seen[ref] {
				queue = append(queue, ref)
			}
		}
	}
	return result
}

// refsOf returns the full ids referenced by the rule named id via join.refs,
// or nil when the rule's file or entry can't be found.
func refsOf(id string, rulesetRoots []string) []string {
	relPath, shortID, ok := splitRuleID(id)
	if !ok {
		return nil
	}
	rf, ok := loadRuleFile(relPath, rulesetRoots)
	if !ok {
		return nil
	}
	for _, r := range rf.Rules {
		if r.ID != shortID {
			continue
		}
		var refs []string
		for _, ref := range r.Join.Refs {
			if full := refToRuleID(ref.Rule, relPath); full != "" {
				refs = append(refs, full)
			}
		}
		return refs
	}
	return nil
}

// splitRuleID splits "java/security/x.yaml:short" into "java/security/x.yaml" and "short".
func splitRuleID(id string) (relPath, shortID string, ok bool) {
	idx := strings.LastIndex(id, ":")
	if idx < 0 {
		return "", "", false
	}
	return id[:idx], id[idx+1:], true
}

// refToRuleID converts a join ref to a full rule id. A cross-file ref is
// "path.yaml#short"; a fragment-less ref names a rule in the referencing file
// itself, so it is qualified with that file's path — mirroring the analyzer's
// resolveRefRuleId, which resolves a bare ref to "<currentFile>:<shortId>".
func refToRuleID(ref, currentRelPath string) string {
	idx := strings.LastIndex(ref, "#")
	if idx < 0 {
		return currentRelPath + ":" + ref
	}
	return ref[:idx] + ":" + ref[idx+1:]
}

// loadRuleFile finds relPath under one of the roots and parses it.
func loadRuleFile(relPath string, rulesetRoots []string) (ruleFile, bool) {
	for _, root := range rulesetRoots {
		data, err := os.ReadFile(filepath.Join(root, filepath.FromSlash(relPath)))
		if err != nil {
			continue
		}
		var rf ruleFile
		if err := yaml.Unmarshal(data, &rf); err != nil {
			continue
		}
		return rf, true
	}
	return ruleFile{}, false
}
