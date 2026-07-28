package triage

import (
	"strings"

	"github.com/seqra/opentaint/internal/sarif"
)

// Gate decides whether a report should fail the build.
//
// A finding counts when it is not suppressed and its level is in scope. With a
// baseline, only findings the comparison could not account for count: "new"
// ones, and ones it could not compare at all (no identity fingerprint), which
// fail closed rather than slipping through unnoticed. "unchanged" and "updated"
// findings existed before and do not fail the build.
type Gate struct {
	// Enabled turns the gate on (--error-on-findings). Off by default, which
	// keeps the historical behavior of never failing on findings.
	Enabled bool
	// Severities restricts which SARIF levels count. Empty means every level.
	Severities []string
}

// Evaluate returns the number of findings that count and whether the gate trips.
func (g Gate) Evaluate(report *sarif.Report, view *sarif.TriageView) (int, bool) {
	if !g.Enabled {
		return 0, false
	}

	count := 0
	for _, r := range report.Results() {
		if sarif.IsSuppressed(r) {
			continue
		}
		if !g.inScope(r) {
			continue
		}
		if !counts(r, view) {
			continue
		}
		count++
	}
	return count, count > 0
}

// counts reports whether a finding is one the gate should care about given the
// baseline comparison, if any.
func counts(r *sarif.Result, view *sarif.TriageView) bool {
	if view == nil || view.Comparison == nil {
		return true
	}
	switch view.Comparison.StateOf(r) {
	case sarif.New:
		return true
	case "":
		// Not comparable against the baseline: fail closed.
		return true
	default:
		return false
	}
}

func (g Gate) inScope(r *sarif.Result) bool {
	return len(g.Severities) == 0 || sarif.MatchesSeverity(r, g.Severities)
}

// ParseGateSeverities validates --error-on-severity values. The flag is
// repeatable, and each value may also be a comma-separated list, so
// "--error-on-severity error,warning" and "--error-on-severity error
// --error-on-severity warning" mean the same thing.
func ParseGateSeverities(values []string) ([]string, error) {
	var out []string
	for _, v := range values {
		for _, token := range strings.Split(v, ",") {
			normalized := strings.ToLower(strings.TrimSpace(token))
			if normalized == "" {
				continue
			}
			if err := sarif.ValidateSeverity(normalized); err != nil {
				return nil, err
			}
			out = append(out, normalized)
		}
	}
	return out, nil
}
