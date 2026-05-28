package sarif

import (
	"fmt"
	"sort"
	"strings"
)

// GroupDimension is the dimension by which the --show-findings listing is grouped.
type GroupDimension int

const (
	groupByFilePath GroupDimension = iota
	groupBySeverity
	groupByRuleID
)

// ListingOptions controls how the --show-findings detailed listing is rendered.
type ListingOptions struct {
	ShowCodeSnippets bool
	VerboseFlow      bool
	MaxNestingLevel  int               // < 0 means "no cap" (legacy flow rendering)
	GroupBy          GroupDimension    // default groupByFilePath
	FingerprintKey   string            // "" = DefaultFingerprintKey
	CodeFlows        CodeFlowSelection // zero value = render first flow only
}

// ParseGroupDimension converts a --group-by flag value into a GroupDimension.
// An empty value selects the default (file-path); unknown values return an error.
func ParseGroupDimension(s string) (GroupDimension, error) {
	switch strings.TrimSpace(strings.ToLower(s)) {
	case "", "file-path":
		return groupByFilePath, nil
	case "severity":
		return groupBySeverity, nil
	case "rule-id":
		return groupByRuleID, nil
	default:
		return 0, fmt.Errorf("invalid --group-by %q: valid values are severity, rule-id, file-path", s)
	}
}

// groupKey returns the section key and display label for a finding under dim.
// key is used for grouping/sorting; label is the section header text.
func groupKey(r *Result, dim GroupDimension) (key, label string) {
	switch dim {
	case groupBySeverity:
		lvl := string(findingLevel(r))
		return lvl, strings.ToUpper(lvl)
	case groupByRuleID:
		id := "<unknown>"
		if r.RuleID != nil && *r.RuleID != "" {
			id = *r.RuleID
		}
		return id, id
	default: // groupByFilePath
		file := "<unknown>"
		if loc, ok := primaryNodeLoc(r); ok && loc.relFilePath != "" {
			file = loc.relFilePath
		}
		return file, file
	}
}

// severityRank orders severity group keys error -> warning -> note -> none.
var severityRank = map[string]int{"error": 0, "warning": 1, "note": 2, "none": 3}

// sortGroups orders section keys deterministically: severity by severityRank,
// rule-id and file-path lexicographically.
func sortGroups(keys []string, dim GroupDimension) {
	if dim == groupBySeverity {
		sort.Slice(keys, func(i, j int) bool {
			ri, oki := severityRank[keys[i]]
			rj, okj := severityRank[keys[j]]
			if !oki {
				ri = 99
			}
			if !okj {
				rj = 99
			}
			if ri != rj {
				return ri < rj
			}
			return keys[i] < keys[j]
		})
		return
	}
	sort.Strings(keys)
}
