package sarif

import (
	"fmt"
	"path"
	"sort"
	"strings"

	"github.com/seqra/opentaint/internal/output"
)

type classifiedStep struct {
	Step ThreadFlowLocation
}

// formatFlowStep formats a single dataflow step into a summary line and a location line.
func formatFlowStep(cs classifiedStep, absProjectPath string) (string, string) {
	step := cs.Step
	loc := step.Location.extractNodeLoc()

	msg := ""
	if step.Location != nil && step.Location.Message != nil && step.Location.Message.Text != nil {
		msg = strings.Join(strings.Fields(*step.Location.Message.Text), " ")
	} else {
		output.LogInfo("ThreadFlowLocation has no message text")
	}

	mainLine := msg

	// Format location as plain text (hyperlinks handled by caller if needed)
	locationLine := fmt.Sprintf("%s:%d", loc.relFilePath, loc.line)

	return mainLine, locationLine
}

// classifyTaintFlowAt returns the ordered taint steps (source -> ... -> sink)
// of the idx-th (0-based) code flow of the given result. It returns an error
// when the result has no code flows, when idx is out of range, or when the
// chosen flow has no thread flows or no locations.
func classifyTaintFlowAt(result *Result, idx int) ([]classifiedStep, error) {
	if len(result.CodeFlows) == 0 {
		return nil, fmt.Errorf("result has no codeFlows")
	}
	if idx < 0 || idx >= len(result.CodeFlows) {
		return nil, fmt.Errorf("code flow index %d out of range (total %d)", idx, len(result.CodeFlows))
	}

	cf := result.CodeFlows[idx]
	if len(cf.ThreadFlows) == 0 {
		return nil, fmt.Errorf("code flow %d has no threadFlows", idx)
	}

	tf := cf.ThreadFlows[0]
	if len(tf.Locations) == 0 {
		return nil, fmt.Errorf("threadFlow has no locations")
	}

	steps := tf.Locations

	sort.Slice(steps, func(i, j int) bool {
		li := getExecutionOrder(steps[i])
		lj := getExecutionOrder(steps[j])
		return li < lj
	})

	out := make([]classifiedStep, 0, len(steps))
	for _, step := range steps {
		out = append(out, classifiedStep{Step: step})
	}

	return out, nil
}

// getExecutionOrder safely extracts execution order from a step
func getExecutionOrder(step ThreadFlowLocation) int64 {
	if step.ExecutionOrder != nil {
		return *step.ExecutionOrder
	}
	output.LogInfo("Missing executionOrder in taint step; treating as 0")
	return 0
}

// stepMethod returns a step's fully-qualified method name (falling back to its
// plain name), or "" when no logical location is present.
func stepMethod(cs classifiedStep) string {
	loc := cs.Step.Location
	if loc == nil || len(loc.LogicalLocations) == 0 {
		return ""
	}
	ll := loc.LogicalLocations[0]
	if ll.FullyQualifiedName != nil {
		return *ll.FullyQualifiedName
	}
	if ll.Name != nil {
		return *ll.Name
	}
	return ""
}

// hasKind reports whether a step's kinds contain the given kind.
func hasKind(cs classifiedStep, kind string) bool {
	for _, k := range cs.Step.Kinds {
		if k == kind {
			return true
		}
	}
	return false
}

// deriveNestingLevels assigns each flow step a call-depth level derived from its
// kinds plus logical-location method identity. A step whose kinds contain "call"
// increases the depth of the steps that follow; a return is inferred when a later
// step's method matches a method already on the frame stack (depth pops back to
// it). SARIF emitted without logical methods degrades to depth that only rises.
func deriveNestingLevels(steps []classifiedStep) []int {
	type frame struct {
		method string
		depth  int
	}
	levels := make([]int, len(steps))
	var stack []frame
	depth := 0
	for i := range steps {
		method := stepMethod(steps[i])
		if method != "" {
			for j := len(stack) - 1; j >= 0; j-- {
				if stack[j].method == method {
					depth = stack[j].depth
					stack = stack[:j]
					break
				}
			}
		}
		levels[i] = depth
		if hasKind(steps[i], "call") {
			stack = append(stack, frame{method: method, depth: depth})
			depth++
		}
	}
	return levels
}

// flowRenderItem is one entry to render in a code flow: either a kept step
// (step != nil) or a "(hidden N steps)" placeholder (hidden > 0).
type flowRenderItem struct {
	step   *classifiedStep
	hidden int
}

// shapeFlow selects which steps to display under a max nesting level, always
// keeping the first (source) and last (sink) step, and emits a placeholder for
// each contiguous run of hidden deeper steps.
func shapeFlow(steps []classifiedStep, maxLevel int) []flowRenderItem {
	levels := deriveNestingLevels(steps)
	var items []flowRenderItem
	hidden := 0
	flush := func() {
		if hidden > 0 {
			items = append(items, flowRenderItem{hidden: hidden})
			hidden = 0
		}
	}
	for i := range steps {
		keep := i == 0 || i == len(steps)-1 || levels[i] <= maxLevel
		if keep {
			flush()
			s := steps[i]
			items = append(items, flowRenderItem{step: &s})
		} else {
			hidden++
		}
	}
	// Defensive: the last step is always kept (i == len(steps)-1), so any pending
	// hidden run is already flushed before it; this final flush is a no-op today.
	flush()
	return items
}

type nodeLoc struct {
	relFilePath string
	fileName    string
	method      string
	line        int64
}

// primaryNodeLoc returns the extracted nodeLoc of r's first location and ok=true.
// When r has no locations it returns the zero nodeLoc and ok=false; callers that
// need a sentinel "line missing" value (e.g. -1) should initialize it themselves.
func primaryNodeLoc(r *Result) (nodeLoc, bool) {
	if len(r.Locations) == 0 {
		return nodeLoc{}, false
	}
	return r.Locations[0].extractNodeLoc(), true
}

func (loc Location) extractNodeLoc() nodeLoc {
	if loc.PhysicalLocation == nil || loc.PhysicalLocation.ArtifactLocation == nil || loc.PhysicalLocation.ArtifactLocation.URI == nil {
		output.LogInfo("Location has no PhysicalLocation/ArtifactLocation/URI")
		return nodeLoc{}
	}

	// For correct file:/// hyperlinks on Windows
	relFilePath := strings.ReplaceAll(*loc.PhysicalLocation.ArtifactLocation.URI, "\\", "/")
	fileName := path.Base(relFilePath)
	var lineVal int64 = -1
	if loc.PhysicalLocation.Region != nil && loc.PhysicalLocation.Region.StartLine != nil {
		lineVal = *loc.PhysicalLocation.Region.StartLine
	} else {
		output.LogInfo("Region or StartLine is nil")
	}

	method := ""
	if len(loc.LogicalLocations) == 0 {
		output.LogInfo("Logical locations is empty, unable to extract method name")
	} else if logicalLoc := loc.LogicalLocations[0]; logicalLoc.FullyQualifiedName != nil {
		method = " " + *logicalLoc.FullyQualifiedName
	}

	return nodeLoc{relFilePath: relFilePath, fileName: fileName, method: method, line: lineVal}
}
