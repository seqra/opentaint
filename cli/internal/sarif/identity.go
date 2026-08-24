package sarif

import (
	"fmt"
	"sort"
	"strings"
)

// Fingerprint keys emitted by the analyzer under result.partialFingerprints,
// from the most exact identity to the coarsest. Every one of them hashes the
// rule id, so a fingerprint never spans two rules.
//
// TraceFingerprintKey adds the sink and every location on every trace: an exact
// identity that changes whenever anything on the flow path moves.
// SourceSinkFingerprintKey adds the sink and the source (first) location of each
// trace, so it survives refactoring of the intermediate call path.
// SinkFingerprintKey adds the sink alone, so it survives any change to where the
// untrusted data comes from.
const (
	TraceFingerprintKey      = "vulnerabilityWithTraceHash/v1"
	SourceSinkFingerprintKey = "vulnerabilitySourceSinkHash/v1"
	SinkFingerprintKey       = "vulnerabilitySinkHash/v1"
)

// IdentityKey is the fingerprint that decides whether a finding in one report
// is "the same finding" as one in another report. It is always the sink hash:
// the sink hash names the vulnerable statement and nothing else, so a decision
// survives every edit to how the untrusted data reaches it. The analyzer
// reports one finding per rule and sink, so the coarsest key loses no findings
// — it only stops them from changing identity. The finer keys never match
// findings across reports. They only describe what moved underneath a finding.
const IdentityKey = SinkFingerprintKey

// refiningKeys are the keys that refine the identity, nearest first. The first
// one that differs between two matched findings is the most meaningful
// description of what changed.
var refiningKeys = []string{SourceSinkFingerprintKey, TraceFingerprintKey}

// Identity returns the result's value for the given fingerprint key. The second
// return is false when the result carries no such fingerprint, which means it
// cannot be matched against a baseline or named in a suppression.
func Identity(r *Result, key string) (string, bool) {
	if r == nil || r.PartialFingerprints == nil {
		return "", false
	}
	v, ok := r.PartialFingerprints[key]
	if !ok || v == "" {
		return "", false
	}
	return v, true
}

// Results returns pointers to every result across every run, so callers can
// annotate results in place.
func (report *Report) Results() []*Result {
	var out []*Result
	for runIdx := range report.Runs {
		run := &report.Runs[runIdx]
		for resultIdx := range run.Results {
			out = append(out, &run.Results[resultIdx])
		}
	}
	return out
}

// ResolvePrefix finds the results whose identity fingerprint starts with
// prefix, git-style. All matches must share one fingerprint value: results
// with the same identity are the same finding to a decision, and one sink
// legitimately appears on several results. A prefix matching two distinct
// values is ambiguous, and an empty or unmatched prefix is an error — a
// decision names a finding, never "whichever matched first".
func ResolvePrefix(report *Report, prefix string) ([]*Result, error) {
	if prefix == "" {
		return nil, fmt.Errorf("fingerprint prefix must not be empty")
	}

	var matches []*Result
	distinct := map[string]bool{}
	for _, r := range report.Results() {
		fp, ok := Identity(r, IdentityKey)
		if !ok || !strings.HasPrefix(fp, prefix) {
			continue
		}
		matches = append(matches, r)
		distinct[fp] = true
	}

	if len(matches) == 0 {
		return nil, fmt.Errorf("no finding matches fingerprint %q", prefix)
	}
	if len(distinct) > 1 {
		values := make([]string, 0, len(distinct))
		for v := range distinct {
			values = append(values, v)
		}
		sort.Strings(values)
		return nil, fmt.Errorf("fingerprint %q is ambiguous, it matches %d findings: %s",
			prefix, len(matches), strings.Join(values, ", "))
	}
	return matches, nil
}
