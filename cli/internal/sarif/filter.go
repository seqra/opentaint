package sarif

import (
	"fmt"
	"strings"

	"github.com/bmatcuk/doublestar/v4"
)

// DefaultFingerprintKey is the partialFingerprints key matched by
// --partial-fingerprint when --partial-fingerprint-key is not supplied.
const DefaultFingerprintKey = "vulnerabilityWithTraceHash/v1"

// Filters describes the finding-selection criteria supplied on the summary
// command. Empty fields mean "do not filter on this dimension".
type Filters struct {
	Paths          []string // doublestar globs against the relative file path
	Severities     []string // SARIF levels: error/warning/note/none
	RuleIDs        []string // full id, leaf, or doublestar glob over the full id
	Fingerprints   []string // git-style prefixes of the chosen fingerprint key's value
	FingerprintKey string   // partialFingerprints key to match ("" = DefaultFingerprintKey)
}

// active reports whether any filter dimension is set. FingerprintKey is
// intentionally excluded: it only selects which key Fingerprints matches
// against, so it has no effect without Fingerprints set.
func (f Filters) active() bool {
	return len(f.Paths) > 0 || len(f.Severities) > 0 || len(f.RuleIDs) > 0 || len(f.Fingerprints) > 0
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
	if len(f.Severities) > 0 && !matchSeverity(r, f.Severities) {
		return false
	}
	if len(f.RuleIDs) > 0 && !matchRuleID(r, f.RuleIDs) {
		return false
	}
	if len(f.Fingerprints) > 0 && !matchFingerprint(r, f.FingerprintKey, f.Fingerprints) {
		return false
	}
	return true
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

// matchSeverity reports whether the result's level equals any supplied level
// (case-insensitive). A nil/empty level is treated as "note".
func matchSeverity(r *Result, levels []string) bool {
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

// matchRuleID reports whether the result's rule-id matches any supplied value as
// a full-id exact match, a leaf exact match, or a doublestar glob over the full id.
func matchRuleID(r *Result, values []string) bool {
	if r.RuleID == nil {
		return false
	}
	full := *r.RuleID
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
// key is used.
func fingerprintValue(r *Result, key string) string {
	if key == "" {
		key = DefaultFingerprintKey
	}
	return r.PartialFingerprints[key]
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
	if validSeverities[strings.ToLower(strings.TrimSpace(level))] {
		return nil
	}
	return fmt.Errorf("invalid --severity %q: valid values are error, warning, note, none", level)
}
