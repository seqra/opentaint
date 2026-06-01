package sarif

import (
	"fmt"
	"path/filepath"
	"sort"
	"strings"

	"charm.land/lipgloss/v2/tree"

	"github.com/seqra/opentaint/internal/output"
)

type endpointInfo struct {
	Route  string
	Params []string
}

func (report *Report) buildFindingTree(out *output.Printer, result *Result, runIdx int, opts ListingOptions) (*tree.Tree, bool) {
	absProjectPath, err := report.projectPath(runIdx)
	if err != nil {
		output.LogInfof("Project path lookup failed: %v", err)
		return nil, false
	}

	if len(result.Locations) == 0 || result.Locations[0].PhysicalLocation == nil {
		output.LogInfo("No primary location for finding")
		return nil, false
	}

	lvl := Level("unknown")
	if result.Level != nil {
		lvl = *result.Level
	} else {
		output.LogInfo("Finding has nil level; defaulting to 'unknown'")
	}

	rule := "<unknown>"
	if result.RuleID != nil {
		rule = *result.RuleID
	} else {
		output.LogInfo("Finding has nil ruleId")
	}

	var ruleDesc string
	var cwe []string
	if ruleMeta := report.ruleByID(runIdx, rule); ruleMeta != nil {
		ruleDesc = ruleDescription(*ruleMeta)
		cwe = cweTags(*ruleMeta)
	}
	if len(cwe) > 0 {
		rule += " [" + strings.Join(cwe, ", ") + "]"
	}

	msg := ""
	if result.Message.Text != nil {
		msg = *result.Message.Text
	} else {
		output.LogInfo("Finding has nil message.text")
	}

	showMessage := strings.TrimSpace(msg) != "" && strings.TrimSpace(msg) != strings.TrimSpace(ruleDesc)

	loc := result.Locations[0]
	nodeLoc := loc.extractNodeLoc()
	locStr := printLocStyled(nodeLoc, absProjectPath, out)

	const msgWrap = 120
	const flowWrap = 117

	th := out.Theme()
	// Prefer the partial fingerprint as the finding header — it is the stable,
	// copy-pasteable identity for triage. When no fingerprint is available
	// (e.g. SARIF generated without generateFingerprint), fall back to the rule
	// id as the header and skip the Rule subfield (it would just duplicate it).
	header := rule
	if fp := fingerprintAbbrev(result, opts.FingerprintKey); fp != "" {
		header = th.FieldKey.Render("Fingerprint:") + " " + fp
	}
	findingNode := out.GroupItem(header)

	if header != rule {
		findingNode.Child(out.FieldItem("Rule", rule))
	}

	severityStr := strings.ToUpper(string(lvl))
	var coloredSeverity string
	switch lvl {
	case Error:
		coloredSeverity = th.Error.Render(severityStr)
	case Warning:
		coloredSeverity = th.Warning.Render(severityStr)
	default:
		coloredSeverity = th.Note.Render(severityStr)
	}
	findingNode.Child(out.FieldItem("Severity", coloredSeverity))
	findingNode.Child(out.FieldItem("Location", locStr))

	total := len(result.CodeFlows)
	if total > 1 {
		findingNode.Child(out.FieldItem("Code flows", total))
	}

	if showMessage {
		findingNode.Child(out.FieldItem("Message", output.WrapText(msg, msgWrap)))
	}

	endpoints := findingEndpoints(result)
	if len(endpoints) > 0 {
		endpointsNode := out.GroupItem(out.Theme().FieldKey.Render("Endpoints:"))
		for _, endpoint := range endpoints {
			endpointLine := endpoint.Route
			if len(endpoint.Params) > 0 {
				endpointLine += " (" + strings.Join(endpoint.Params, ", ") + ")"
			}
			endpointsNode.Child(endpointLine)
		}
		findingNode.Child(endpointsNode)
		findingNode.Child("")
	}

	if total == 0 {
		// No code flows: render a snippet on the result location, matching legacy.
		resultPath := extractAbsolutePath(&loc, absProjectPath, "Result")
		if resultPath != "" && opts.ShowCodeSnippets {
			snippet := out.Snippet().LoadOrEmpty(resultPath, loc.extractNodeLoc().line)
			if snippet != "" {
				findingNode.Child("Code snippet\n" + snippet)
			}
		}
		return findingNode, false
	}

	indices := opts.CodeFlows.selectedIndices(total)
	omitted := false

	for _, i := range indices {
		taintFlow, classifyErr := classifyTaintFlowAt(result, i-1)
		if classifyErr != nil {
			output.LogDebugf("No source/sink for flow %d: %s", i, classifyErr)
			continue
		}

		flowHeader := "Code flow:"
		if total > 1 {
			flowHeader = fmt.Sprintf("Code flow (%d of %d):", i, total)
		}
		flowTree := out.GroupItem(out.Theme().FieldKey.Render(flowHeader))
		shownSnippets := make(map[string]struct{})

		if opts.MaxNestingLevel >= 0 {
			firstStep := true
			for _, it := range shapeFlow(taintFlow, opts.MaxNestingLevel) {
				if it.step == nil {
					// Hidden runs flip `omitted` (so the "verbose-flow" suggestion
					// still fires), but no per-gap placeholder is rendered.
					omitted = true
					continue
				}
				if !firstStep && opts.ShowCodeSnippets {
					flowTree.Child("")
				}
				report.renderFlowStep(out, flowTree, *it.step, absProjectPath, opts.ShowCodeSnippets, shownSnippets, flowWrap)
				firstStep = false
			}
		} else {
			flowSteps := taintFlow
			if !opts.VerboseFlow && len(taintFlow) > 2 {
				flowSteps = []classifiedStep{taintFlow[0], taintFlow[len(taintFlow)-1]}
				omitted = true
			}
			for j, cs := range flowSteps {
				report.renderFlowStep(out, flowTree, cs, absProjectPath, opts.ShowCodeSnippets, shownSnippets, flowWrap)
				if !opts.VerboseFlow && len(flowSteps) == 2 && j == 0 {
					flowTree.Child("")
				}
				if opts.VerboseFlow && opts.ShowCodeSnippets && j < len(flowSteps)-1 {
					flowTree.Child("")
				}
			}
		}

		findingNode.Child(flowTree)
	}

	return findingNode, omitted
}

func printLocStyled(loc nodeLoc, absProjectPath string, out *output.Printer) string {
	return out.FileLink(absProjectPath, loc.relFilePath, loc.relFilePath, loc.line)
}

func (report *Report) ruleByID(runIdx int, ruleID string) *ReportingDescriptor {
	if ruleID == "" || runIdx < 0 || runIdx >= len(report.Runs) {
		return nil
	}

	run := report.Runs[runIdx]
	for i := range run.Tool.Driver.Rules {
		if run.Tool.Driver.Rules[i].ID == ruleID {
			return &run.Tool.Driver.Rules[i]
		}
	}

	for runIndex := range report.Runs {
		for i := range report.Runs[runIndex].Tool.Driver.Rules {
			if report.Runs[runIndex].Tool.Driver.Rules[i].ID == ruleID {
				return &report.Runs[runIndex].Tool.Driver.Rules[i]
			}
		}
	}

	return nil
}

func findingEndpoints(result *Result) []endpointInfo {
	if result == nil || len(result.RelatedLocations) == 0 {
		return nil
	}

	type endpointBuilder struct {
		route  string
		params map[string]struct{}
	}

	byRoute := make(map[string]*endpointBuilder)

	for _, related := range result.RelatedLocations {
		for _, logical := range related.LogicalLocations {
			endpoint := ""
			if logical.FullyQualifiedName != nil {
				endpoint = strings.TrimSpace(*logical.FullyQualifiedName)
			}
			if endpoint == "" {
				if logical.Name != nil {
					endpoint = strings.TrimSpace(*logical.Name)
				}
			}
			if endpoint == "" {
				continue
			}

			builder, exists := byRoute[endpoint]
			if !exists {
				builder = &endpointBuilder{route: endpoint, params: make(map[string]struct{})}
				byRoute[endpoint] = builder
			}

			tags := []string{}
			if logical.Properties != nil {
				tags = logical.Properties.Tags
			}
			if len(tags) > 0 {
				for _, tag := range tags {
					tag = strings.TrimSpace(tag)
					if tag == "" {
						continue
					}
					builder.params[tag] = struct{}{}
				}
			}
		}
	}

	routes := make([]string, 0, len(byRoute))
	for route := range byRoute {
		routes = append(routes, route)
	}
	sort.Strings(routes)

	endpoints := make([]endpointInfo, 0, len(routes))
	for _, route := range routes {
		builder := byRoute[route]
		params := make([]string, 0, len(builder.params))
		for param := range builder.params {
			params = append(params, param)
		}
		sort.Strings(params)
		endpoints = append(endpoints, endpointInfo{Route: route, Params: params})
	}

	return endpoints
}

// fingerprintAbbrev returns a short, git-style prefix of the result's
// partialFingerprints value under key, for display in the listing. Returns ""
// when the key is absent. When key is empty the default key is used.
func fingerprintAbbrev(result *Result, key string) string {
	val := fingerprintValue(result, key)
	if val == "" {
		return ""
	}
	const n = 12
	if len(val) > n {
		return val[:n]
	}
	return val
}

// renderFlowStep adds one thread-flow step (with an optional code snippet) to
// the flow tree, de-duplicating snippets via shownSnippets.
func (report *Report) renderFlowStep(out *output.Printer, flowTree *tree.Tree, cs classifiedStep, absProjectPath string, showCodeSnippets bool, shownSnippets map[string]struct{}, flowWrap int) {
	mainLine, locationLine := formatFlowStep(cs, absProjectPath)
	mainLine = output.WrapText(mainLine, flowWrap)
	stepNode := out.GroupItem(mainLine, locationLine)

	stepLoc := cs.Step.Location
	locPath := extractAbsolutePath(stepLoc, absProjectPath, "Flow")
	if locPath != "" && showCodeSnippets {
		line := stepLoc.extractNodeLoc().line
		snippetKey := fmt.Sprintf("%s:%d", locPath, line)
		if _, alreadyShown := shownSnippets[snippetKey]; !alreadyShown {
			snippet := out.Snippet().LoadOrEmpty(locPath, line)
			if snippet != "" {
				stepNode.Child("Code snippet\n" + snippet)
				shownSnippets[snippetKey] = struct{}{}
			}
		}
	}
	flowTree.Child(stepNode)
}

func extractAbsolutePath(location *Location, absProjectPath, locationName string) string {
	if location != nil &&
		location.PhysicalLocation != nil &&
		location.PhysicalLocation.ArtifactLocation != nil &&
		location.PhysicalLocation.ArtifactLocation.URI != nil {
		return filepath.Join(absProjectPath, *location.PhysicalLocation.ArtifactLocation.URI)
	}
	output.LogInfof("%s location has no URI; snippet path will be empty", locationName)
	return ""
}

func (report *Report) projectPath(runIdx int) (string, error) {
	run := report.Runs[runIdx]

	if base, ok := run.OriginalURIBaseIDS["%SRCROOT%"]; ok {
		if base.URI == nil {
			output.LogInfo("%SRCROOT% base has nil URI")
			return "", fmt.Errorf("%%SRCROOT%% URI is nil")
		}
		return *base.URI, nil
	}
	return "", fmt.Errorf("%%SRCROOT%% not found in OriginalURIBaseIDS")
}
