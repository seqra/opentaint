package sarif

import (
	"fmt"
	"strconv"
	"strings"
)

// CodeFlowSelection describes which code flow(s) of a finding to render.
// The zero value (All=false, Index=0) means "render the first flow only",
// matching the default behavior when --code-flow is not set.
type CodeFlowSelection struct {
	All   bool // render every code flow
	Index int  // 1-based; 0 means unset/default (render first)
}

// ParseCodeFlowSelection converts a --code-flow flag value into a
// CodeFlowSelection. An empty/whitespace value selects the default (first
// only); "all" (case-insensitive) selects all flows; a positive integer
// selects that 1-based flow. Other values (including 0, negatives, and
// non-integers) return an error.
func ParseCodeFlowSelection(s string) (CodeFlowSelection, error) {
	t := strings.TrimSpace(s)
	if t == "" {
		return CodeFlowSelection{}, nil
	}
	if strings.EqualFold(t, "all") {
		return CodeFlowSelection{All: true}, nil
	}
	n, err := strconv.Atoi(t)
	if err != nil || n <= 0 {
		return CodeFlowSelection{}, fmt.Errorf("invalid --code-flow %q: expected \"all\" or a positive integer", s)
	}
	return CodeFlowSelection{Index: n}, nil
}

// selectedIndices returns the 1-based code-flow indices to render for a
// finding whose total flow count is `total`. Returns nil when nothing
// should be rendered (finding has zero flows, or the requested index is
// out of range).
func (sel CodeFlowSelection) selectedIndices(total int) []int {
	if total <= 0 {
		return nil
	}
	if sel.All {
		out := make([]int, total)
		for i := range out {
			out[i] = i + 1
		}
		return out
	}
	if sel.Index > 0 {
		if sel.Index > total {
			return nil
		}
		return []int{sel.Index}
	}
	return []int{1}
}
