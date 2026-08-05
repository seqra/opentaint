package sarif

import (
	"crypto/rand"
	"fmt"
)

// Comparison is the classification of a report's results against a baseline
// report. States are keyed by result pointer, so a Comparison is only valid for
// the exact *Report it was computed from.
type Comparison struct {
	states map[*Result]BaselineState

	// Counts holds the number of current results in each state, plus the number
	// of baseline results with no match in the current report under Absent.
	Counts map[BaselineState]int
	// Absent lists the baseline results that no longer appear — the fixed
	// findings. They are reported, never written back into the current report.
	Absent []*Result
	// NotRun lists baseline results whose rule did not run in the current scan,
	// so their absence says nothing about whether they were fixed. Counting them
	// as fixed would report a rule exclusion as a wave of resolved findings.
	NotRun []*Result
	// Unmatchable counts current results carrying no identity fingerprint, which
	// therefore cannot be compared at all.
	Unmatchable int
	// BaselineGUID is the baseline run's automation guid, or "" if it has none.
	BaselineGUID string
}

// StateOf returns the state computed for a result, or "" when the result could
// not be matched (no identity fingerprint).
func (c *Comparison) StateOf(r *Result) BaselineState {
	if c == nil {
		return ""
	}
	return c.states[r]
}

// CompareToBaseline classifies every result in current against baseline, using
// key as the identity fingerprint. Results that match are additionally compared
// on the full-trace fingerprint to tell "unchanged" from "updated".
//
// A baseline that holds results but none carrying key is rejected: silently
// classifying everything as new would hide exactly the findings a baseline
// exists to remember.
func CompareToBaseline(current, baseline *Report, key string) (*Comparison, error) {
	baselineResults := baseline.Results()

	byIdentity := make(map[string][]*Result, len(baselineResults))
	for _, r := range baselineResults {
		id, ok := Identity(r, key)
		if !ok {
			continue
		}
		byIdentity[id] = append(byIdentity[id], r)
	}
	if len(baselineResults) > 0 && len(byIdentity) == 0 {
		return nil, fmt.Errorf(
			"no result in the baseline carries the %q fingerprint; "+
				"it was produced with a different fingerprint key or without fingerprints", key)
	}

	cmp := &Comparison{
		states:       make(map[*Result]BaselineState),
		Counts:       make(map[BaselineState]int),
		BaselineGUID: baseline.RunGUID(),
	}

	matched := make(map[string]bool, len(byIdentity))
	for _, r := range current.Results() {
		id, ok := Identity(r, key)
		if !ok {
			cmp.Unmatchable++
			continue
		}

		previous, found := byIdentity[id]
		if !found {
			cmp.states[r] = New
			cmp.Counts[New]++
			continue
		}

		matched[id] = true
		state := Updated
		if sameTrace(r, previous) {
			state = Unchanged
		}
		cmp.states[r] = state
		cmp.Counts[state]++
	}

	executed := current.executedRuleIDs()
	for id, results := range byIdentity {
		if matched[id] {
			continue
		}
		for _, r := range results {
			if !ranInCurrentScan(r, executed) {
				cmp.NotRun = append(cmp.NotRun, r)
				continue
			}
			cmp.Absent = append(cmp.Absent, r)
		}
	}
	cmp.Counts[Absent] = len(cmp.Absent)

	return cmp, nil
}

// WithAbsent returns a shallow copy of the report whose first run also carries
// the given baseline results, each stamped absent. It exists so that the fixed
// findings — which live in the baseline and never in the current report — can be
// listed on request. Only the display path calls it; the copies never reach a
// report that is written back.
func (report *Report) WithAbsent(absent []*Result) *Report {
	if len(absent) == 0 || len(report.Runs) == 0 {
		return report
	}

	out := *report
	out.Runs = make([]Run, len(report.Runs))
	copy(out.Runs, report.Runs)

	run := out.Runs[0]
	results := make([]Result, 0, len(run.Results)+len(absent))
	results = append(results, run.Results...)
	for _, r := range absent {
		fixed := *r
		state := Absent
		fixed.BaselineState = &state
		results = append(results, fixed)
	}
	run.Results = results
	out.Runs[0] = run
	return &out
}

// executedRuleIDs returns the ids of the rules the run declares it executed, or
// nil when the report declares none — in which case nothing can be said about
// which rules ran and every unmatched baseline finding is treated as fixed.
func (report *Report) executedRuleIDs() map[string]bool {
	ids := map[string]bool{}
	for i := range report.Runs {
		for _, rule := range report.Runs[i].Tool.Driver.Rules {
			if rule.ID != "" {
				ids[rule.ID] = true
			}
		}
	}
	if len(ids) == 0 {
		return nil
	}
	return ids
}

// ranInCurrentScan reports whether the rule behind a baseline result was part of
// the current scan. A result without a rule id is assumed to have run: guessing
// "excluded" would hide a genuinely fixed finding.
func ranInCurrentScan(r *Result, executed map[string]bool) bool {
	if executed == nil || r.RuleID == nil || *r.RuleID == "" {
		return true
	}
	return executed[*r.RuleID]
}

// sameTrace reports whether the current result's full-trace fingerprint equals
// that of any baseline result sharing its identity. A missing trace fingerprint
// on either side counts as unchanged: the finer comparison is unavailable, and
// claiming "updated" on missing data would be noise.
func sameTrace(current *Result, previous []*Result) bool {
	currentTrace, ok := Identity(current, TraceFingerprintKey)
	if !ok {
		return true
	}
	for _, p := range previous {
		previousTrace, ok := Identity(p, TraceFingerprintKey)
		if !ok || previousTrace == currentTrace {
			return true
		}
	}
	return false
}

// Apply writes the comparison into the report: result.baselineState on every
// matched result, and run.baselineGuid on every run when the baseline had a
// guid to cite. Unmatchable results are left untouched.
func (c *Comparison) Apply(report *Report) {
	for _, r := range report.Results() {
		state, ok := c.states[r]
		if !ok {
			continue
		}
		value := state
		r.BaselineState = &value
	}
	if c.BaselineGUID == "" {
		return
	}
	for i := range report.Runs {
		guid := c.BaselineGUID
		report.Runs[i].BaselineGUID = &guid
	}
}

// RunGUID returns the first run's automation guid, or "" when absent. This is
// what a later run cites as its baselineGuid.
func (report *Report) RunGUID() string {
	for i := range report.Runs {
		if details := report.Runs[i].AutomationDetails; details != nil && details.GUID != nil {
			return *details.GUID
		}
	}
	return ""
}

// EnsureRunGUIDs stamps a v4 GUID into run.automationDetails.guid for every run
// that lacks one. The analyzer emits no automation details, so without this no
// report could ever be cited as a baseline by guid. Existing guids are kept.
func EnsureRunGUIDs(report *Report) {
	for i := range report.Runs {
		run := &report.Runs[i]
		if run.AutomationDetails == nil {
			run.AutomationDetails = &RunAutomationDetails{}
		}
		if run.AutomationDetails.GUID != nil && *run.AutomationDetails.GUID != "" {
			continue
		}
		guid := newUUIDv4()
		run.AutomationDetails.GUID = &guid
	}
}

// newUUIDv4 returns a random RFC 4122 version 4 UUID. Hand-rolled to avoid a
// dependency for sixteen bytes; rand.Read is documented never to fail.
func newUUIDv4() string {
	var b [16]byte
	if _, err := rand.Read(b[:]); err != nil {
		panic(fmt.Sprintf("crypto/rand failed: %v", err))
	}
	b[6] = (b[6] & 0x0f) | 0x40 // version 4
	b[8] = (b[8] & 0x3f) | 0x80 // variant 10
	return fmt.Sprintf("%x-%x-%x-%x-%x", b[0:4], b[4:6], b[6:8], b[8:10], b[10:16])
}
