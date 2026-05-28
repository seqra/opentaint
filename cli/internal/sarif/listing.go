package sarif

import (
	"fmt"
	"sort"

	"github.com/seqra/opentaint/internal/output"
)

// PrintAll renders every finding in report as a grouped, sorted listing. It
// returns true when at least one finding had its code flow truncated (so the
// caller can offer a "--verbose-flow" hint). Groups are determined by
// opts.GroupBy and ordered by sortGroups; within a group, findings sort by
// file path, then start line (missing lines last), then original SARIF order.
func (report *Report) PrintAll(out *output.Printer, opts ListingOptions) bool {
	totalFindings := 0
	for _, run := range report.Runs {
		totalFindings += len(run.Results)
	}
	if totalFindings == 0 {
		return false
	}

	type findingRef struct {
		runIdx int
		result *Result
		file   string
		line   int64
		order  int
	}

	byGroup := make(map[string][]findingRef)
	labels := make(map[string]string)
	order := 0

	for runIdx := range report.Runs {
		run := &report.Runs[runIdx]
		for resultIdx := range run.Results {
			order++
			result := &run.Results[resultIdx]

			file := "<unknown>"
			line := int64(-1)
			if loc, ok := primaryNodeLoc(result); ok {
				if loc.relFilePath != "" {
					file = loc.relFilePath
				}
				line = loc.line
			}

			key, label := groupKey(result, opts.GroupBy)
			labels[key] = label
			byGroup[key] = append(byGroup[key], findingRef{
				runIdx: runIdx,
				result: result,
				file:   file,
				line:   line,
				order:  order,
			})
		}
	}

	keys := make([]string, 0, len(byGroup))
	for k := range byGroup {
		keys = append(keys, k)
	}
	sortGroups(keys, opts.GroupBy)

	hasOmitted := false
	for keyIdx, key := range keys {
		group := byGroup[key]
		sort.Slice(group, func(i, j int) bool {
			if group[i].file != group[j].file {
				return group[i].file < group[j].file
			}
			if group[i].line != group[j].line {
				li := group[i].line
				lj := group[j].line
				if li < 0 {
					li = 1<<62 - 1
				}
				if lj < 0 {
					lj = 1<<62 - 1
				}
				return li < lj
			}
			return group[i].order < group[j].order
		})

		section := out.Section(fmt.Sprintf("%s [%d]", labels[key], len(group)))
		for findingIdx, finding := range group {
			if findingIdx > 0 {
				section.Line()
			}
			node, omitted := report.buildFindingTree(out, finding.result, finding.runIdx, opts)
			if node != nil {
				section.Child(node)
			}
			if omitted {
				hasOmitted = true
			}
		}
		section.Render()
		if keyIdx < len(keys)-1 {
			out.Blank()
		}
	}

	return hasOmitted
}
