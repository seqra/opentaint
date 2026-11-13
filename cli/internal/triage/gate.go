package triage

import (
	"strings"

	"github.com/seqra/opentaint/internal/sarif"
)

// Gate decides whether a report should fail the build.
//
// A finding counts when its level is in scope.
type Gate struct {
	// Enabled turns the gate on (--error-on-findings). Off by default, which
	// keeps the historical behavior of never failing on findings.
	Enabled bool
	// Severities restricts which SARIF levels count. Empty means every level.
	Severities []string
}

// Evaluate returns the number of findings that count and whether the gate trips.
func (g Gate) Evaluate(report *sarif.Report) (int, bool) {
	if !g.Enabled {
		return 0, false
	}

	count := 0
	for _, run := range report.Runs {
		for i := range run.Results {
			r := &run.Results[i]
			if !g.inScope(r) {
				continue
			}
			count++
		}
	}
	return count, count > 0
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
			if err := sarif.ValidateSeverityFor("--error-on-severity", normalized); err != nil {
				return nil, err
			}
			out = append(out, normalized)
		}
	}
	return out, nil
}
