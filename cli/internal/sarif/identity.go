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

// identityAliases are the short names accepted for the keys above, so a user
// writes --fingerprint-key sink rather than the versioned SARIF key.
var identityAliases = map[string]string{
	"trace":       TraceFingerprintKey,
	"source-sink": SourceSinkFingerprintKey,
	"sourcesink":  SourceSinkFingerprintKey,
	"sink":        SinkFingerprintKey,
}

// IdentityAliases lists the short names in coarsening order, for help text.
var IdentityAliases = []string{"trace", "source-sink", "sink"}

// DefaultIdentityKey is the fingerprint key used to decide whether a finding in
// one report is "the same finding" as one in another report. The source/sink
// hash is the default because a suppression or baseline entry should survive
// edits to helper methods the flow happens to pass through.
const DefaultIdentityKey = SourceSinkFingerprintKey

// ResolveIdentityKey normalizes a user-supplied identity key, falling back to
// DefaultIdentityKey when unset and expanding the short aliases. Any other key
// is accepted as written — a report may carry fingerprints this build does not
// know about — but a blank one is rejected rather than silently matching
// nothing.
func ResolveIdentityKey(key string) (string, error) {
	if key == "" {
		return DefaultIdentityKey, nil
	}
	trimmed := strings.TrimSpace(key)
	if trimmed == "" {
		return "", fmt.Errorf("fingerprint key must not be blank")
	}
	if full, ok := identityAliases[strings.ToLower(trimmed)]; ok {
		return full, nil
	}
	return trimmed, nil
}

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

// ResolvePrefix finds the single result whose identity fingerprint starts with
// prefix, git-style. An empty, unmatched, or ambiguous prefix is an error: a
// suppression must name exactly one finding, never "whichever matched first".
func ResolvePrefix(report *Report, key, prefix string) (*Result, error) {
	if prefix == "" {
		return nil, fmt.Errorf("fingerprint prefix must not be empty")
	}

	var matches []*Result
	var values []string
	for _, r := range report.Results() {
		fp, ok := Identity(r, key)
		if !ok || !strings.HasPrefix(fp, prefix) {
			continue
		}
		matches = append(matches, r)
		values = append(values, fp)
	}

	switch len(matches) {
	case 0:
		return nil, fmt.Errorf("no finding matches fingerprint %q (key %s)", prefix, key)
	case 1:
		return matches[0], nil
	default:
		sort.Strings(values)
		return nil, fmt.Errorf("fingerprint %q is ambiguous, it matches %d findings: %s",
			prefix, len(matches), strings.Join(values, ", "))
	}
}
