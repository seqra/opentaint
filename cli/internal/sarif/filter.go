package sarif

import (
	"fmt"
	"strings"

	"github.com/bmatcuk/doublestar/v4"
)

// Filters describes the finding-selection criteria supplied on the summary
// command. Empty fields mean "do not filter on this dimension".
type Filters struct {
	Paths          []string // doublestar globs against the relative file path
	Severities     []string // SARIF levels: error/warning/note/none
	RuleIDs        []string // full id, leaf, or doublestar glob over the full id
	Fingerprints   []string // git-style prefixes of the chosen fingerprint key's value
	FingerprintKey string   // partialFingerprints key to match ("" = DefaultIdentityKey)
	BaselineStates []string // SARIF baselineState values: new/unchanged/updated/absent
}

// active reports whether any filter dimension is set. FingerprintKey is
// intentionally excluded: it only selects which key Fingerprints matches
// against, so it has no effect without Fingerprints set.
func (f Filters) active() bool {
	return len(f.Paths) > 0 || len(f.Severities) > 0 || len(f.RuleIDs) > 0 ||
		len(f.Fingerprints) > 0 || len(f.BaselineStates) > 0
}

// Filter returns a shallow copy of the report whose Runs[].Results contain only
// the findings matching every supplied filter dimension. Tool.Driver.Rules and
// OriginalURIBaseIDS are preserved so "Rules executed" stays the full set. When
// no dimension is set, the original report is returned unchanged.
func (report *Report) Filter(f Filters) *Report {
	if !f.active() {
		return report
	}

	out := *report
	out.Runs = make([]Run, len(report.Runs))
	for i := range report.Runs {
		run := report.Runs[i] // shallow copy; Tool/OriginalURIBaseIDS shared
		kept := make([]Result, 0, len(run.Results))
		for j := range run.Results {
			if f.matches(&run.Results[j]) {
				kept = append(kept, run.Results[j])
			}
		}
		run.Results = kept
		out.Runs[i] = run
	}
	return &out
}

// matches reports whether a single result satisfies every supplied filter
// dimension (AND across dimensions; OR within a dimension).
func (f Filters) matches(r *Result) bool {
	if len(f.Paths) > 0 && !matchPath(r, f.Paths) {
		return false
	}
	if len(f.Severities) > 0 && !MatchesSeverity(r, f.Severities) {
		return false
	}
	if len(f.RuleIDs) > 0 && !matchRuleID(r, f.RuleIDs) {
		return false
	}
	if len(f.Fingerprints) > 0 && !matchFingerprint(r, f.FingerprintKey, f.Fingerprints) {
		return false
	}
	if len(f.BaselineStates) > 0 && !matchBaselineState(r, f.BaselineStates) {
		return false
	}
	return true
}

// matchesAs is matches for a result whose baseline state is known from the
// comparison rather than carried on the result itself. Fixed findings live in
// the baseline report and are never stamped with a state, so they can only be
// filtered by a caller that already knows what they are.
func (f Filters) matchesAs(r *Result, state BaselineState) bool {
	if len(f.BaselineStates) > 0 && !stateNamed(state, f.BaselineStates) {
		return false
	}
	stateless := f
	stateless.BaselineStates = nil
	return stateless.matches(r)
}

// WantsAbsent reports whether the filter asks for fixed findings, which the
// caller must add to the listing from the baseline: they exist nowhere in the
// current report.
func (f Filters) WantsAbsent() bool {
	return stateNamed(Absent, f.BaselineStates)
}

// stateNamed reports whether states names the given baseline state.
func stateNamed(state BaselineState, states []string) bool {
	for _, s := range states {
		if strings.EqualFold(strings.TrimSpace(s), string(state)) {
			return true
		}
	}
	return false
}

// matchBaselineState reports whether the result's baselineState equals any
// supplied value (case-insensitive). A result with no baselineState never
// matches: it was not compared against a baseline, so no state claim holds.
func matchBaselineState(r *Result, states []string) bool {
	if r.BaselineState == nil {
		return false
	}
	actual := strings.ToLower(string(*r.BaselineState))
	for _, s := range states {
		if strings.ToLower(strings.TrimSpace(s)) == actual {
			return true
		}
	}
	return false
}

// ParseBaselineStates validates --baseline-state values against the SARIF
// enumeration, returning them normalized.
func ParseBaselineStates(values []string) ([]string, error) {
	valid := map[string]BaselineState{
		"new":       New,
		"unchanged": Unchanged,
		"updated":   Updated,
		"absent":    Absent,
	}
	var out []string
	for _, v := range values {
		normalized := strings.ToLower(strings.TrimSpace(v))
		if normalized == "" {
			continue
		}
		state, ok := valid[normalized]
		if !ok {
			return nil, fmt.Errorf(
				"invalid baseline state %q: valid values are new, unchanged, updated, absent", v)
		}
		out = append(out, string(state))
	}
	return out, nil
}

// matchPath reports whether the result's primary location's relative file path
// matches any of the doublestar glob patterns.
func matchPath(r *Result, patterns []string) bool {
	loc, ok := primaryNodeLoc(r)
	if !ok || loc.relFilePath == "" {
		return false
	}
	rel := loc.relFilePath
	for _, p := range patterns {
		if p == "" {
			continue
		}
		if ok, _ := doublestar.Match(p, rel); ok {
			return true
		}
	}
	return false
}

// MatchesSeverity reports whether the result's level equals any supplied level
// (case-insensitive). A nil/empty level is treated as "note".
func MatchesSeverity(r *Result, levels []string) bool {
	actual := strings.ToLower(string(findingLevel(r)))
	for _, l := range levels {
		if strings.ToLower(strings.TrimSpace(l)) == actual {
			return true
		}
	}
	return false
}

// ruleLeaf returns the leaf rule name: the part after the first ':' for raw
// "ruleSetName:rule-name" ids, or after the last '.' for semgrep-style dotted
// ids, mirroring SemgrepRuleUtils. Returns id unchanged when neither is present.
func ruleLeaf(id string) string {
	if i := strings.IndexByte(id, ':'); i >= 0 {
		return id[i+1:]
	}
	if i := strings.LastIndexByte(id, '.'); i >= 0 {
		return id[i+1:]
	}
	return id
}

// matchRuleID reports whether the result's rule-id matches any supplied value.
func matchRuleID(r *Result, values []string) bool {
	return r.RuleID != nil && MatchesRuleID(*r.RuleID, values)
}

// MatchesRuleID reports whether a rule id matches any supplied value as a
// full-id exact match, a leaf exact match, or a doublestar glob over the full
// id — globs deliberately never match the bare leaf. This is the one rule-id
// grammar: summary's --rule-id filter and scan's rules.only/rules.exclude and
// --exclude-rule-id selection all use it.
func MatchesRuleID(full string, values []string) bool {
	leaf := ruleLeaf(full)
	for _, v := range values {
		// skip blank values (cobra StringArrayVar can yield them) so an empty
		// value never matches a result whose rule id is also empty
		if v == "" {
			continue
		}
		if v == full || v == leaf {
			return true
		}
		if ok, _ := doublestar.Match(v, full); ok {
			return true
		}
	}
	return false
}

// fingerprintValue returns the result's partialFingerprints value under key, or
// "" when the key is absent or its value is empty. When key is empty the default
// identity key is used — the same one triage resolves prefixes against, so a
// fingerprint shown in the listing can always be pasted into triage --accept.
func fingerprintValue(r *Result, key string) string {
	if key == "" {
		key = DefaultIdentityKey
	}
	v, _ := Identity(r, key)
	return v
}

// matchFingerprint reports whether the result's partialFingerprints value under
// key has any supplied value as a prefix (git short-hash style). When key is
// empty the default key is used.
func matchFingerprint(r *Result, key string, prefixes []string) bool {
	val := fingerprintValue(r, key)
	if val == "" {
		return false
	}
	for _, p := range prefixes {
		if p != "" && strings.HasPrefix(val, p) {
			return true
		}
	}
	return false
}

// validSeverities is the set of SARIF levels accepted by --severity.
var validSeverities = map[string]bool{"error": true, "warning": true, "note": true, "none": true}

// ValidateSeverity returns an error if level is not a recognized SARIF level.
func ValidateSeverity(level string) error {
	return ValidateSeverityFor("--severity", level)
}

// ValidateSeverityFor is ValidateSeverity for a caller whose flag is not
// --severity, so the message names the flag the user actually typed.
func ValidateSeverityFor(flag, level string) error {
	if validSeverities[strings.ToLower(strings.TrimSpace(level))] {
		return nil
	}
	return fmt.Errorf("invalid %s %q: valid values are error, warning, note, none", flag, level)
}
