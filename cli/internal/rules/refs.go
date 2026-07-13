package rules

import (
	"os"
	"path/filepath"
	"strings"

	"gopkg.in/yaml.v2"
)

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

func splitRuleID(id string) (relPath, shortID string, ok bool) {
	idx := strings.LastIndex(id, ":")
	if idx < 0 {
		return "", "", false
	}
	return id[:idx], id[idx+1:], true
}

func refToRuleID(ref, currentRelPath string) string {
	idx := strings.LastIndex(ref, "#")
	if idx < 0 {
		return currentRelPath + ":" + ref
	}
	return ref[:idx] + ":" + ref[idx+1:]
}

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
