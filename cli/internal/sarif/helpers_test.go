package sarif

// Test builders for constructing SARIF reports in-memory.

func strptr(s string) *string { return &s }
func lvlptr(l Level) *Level   { return &l }
func i64(v int64) *int64      { return &v }

// makeResult builds a Result with a primary location, level, rule id, and
// optional partial fingerprints.
func makeResult(ruleID string, level Level, relPath string, line int64, fingerprints map[string]string) Result {
	return Result{
		RuleID: strptr(ruleID),
		Level:  lvlptr(level),
		Locations: []Location{{
			PhysicalLocation: &PhysicalLocation{
				ArtifactLocation: &ArtifactLocation{URI: strptr(relPath)},
				Region:           &Region{StartLine: i64(line)},
			},
		}},
		PartialFingerprints: fingerprints,
	}
}

// makeReport wraps results in a single run with a %SRCROOT% base so that
// buildFindingTree's projectPath() lookup succeeds.
func makeReport(results ...Result) *Report {
	return &Report{Runs: []Run{{
		OriginalURIBaseIDS: map[string]ArtifactLocation{"%SRCROOT%": {URI: strptr("/project")}},
		Results:            results,
	}}}
}

// makeStep builds a thread-flow step with an execution order, kinds, and an
// optional fully-qualified method name.
func makeStep(order int64, kinds []string, method string) ThreadFlowLocation {
	loc := &Location{}
	if method != "" {
		loc.LogicalLocations = []LogicalLocation{{FullyQualifiedName: strptr(method)}}
	}
	return ThreadFlowLocation{ExecutionOrder: i64(order), Kinds: kinds, Location: loc}
}

// makeFlowResult builds a Result whose single code flow contains the given steps.
func makeFlowResult(ruleID string, level Level, relPath string, line int64, steps ...ThreadFlowLocation) Result {
	r := makeResult(ruleID, level, relPath, line, nil)
	r.CodeFlows = []CodeFlow{{ThreadFlows: []ThreadFlow{{Locations: steps}}}}
	return r
}

// makeMultiFlowResult builds a Result with `flowCount` code flows. Each flow
// carries two steps (source/sink) with distinct execution orders so they
// classify correctly.
func makeMultiFlowResult(ruleID string, level Level, relPath string, line int64, flowCount int) Result {
	r := makeResult(ruleID, level, relPath, line, nil)
	r.CodeFlows = make([]CodeFlow, flowCount)
	for fi := range r.CodeFlows {
		r.CodeFlows[fi] = CodeFlow{ThreadFlows: []ThreadFlow{{
			Locations: []ThreadFlowLocation{
				makeStep(int64(fi*10+1), []string{"source"}, "src"),
				makeStep(int64(fi*10+2), []string{"sink"}, "sink"),
			},
		}}}
	}
	return r
}
