package triage

import (
	"strings"

	"github.com/seqra/opentaint/internal/sarif"
)

// Gate fails the scan when the report has findings of the selected severities.
type Gate struct {
	// Enabled is --error-on-findings or --error-on-severity.
	Enabled bool
	// Severities are the levels that count; empty means every level.
	Severities []string
}

// Evaluate returns the number of findings that count and whether the gate fails the scan.
func (g Gate) Evaluate(report *sarif.Report) (int, bool) {
	if !g.Enabled {
		return 0, false
	}

	count := 0
	for _, run := range report.Runs {
		for i := range run.Results {
			if g.inScope(&run.Results[i]) {
				count++
			}
		}
	}
	return count, count > 0
}

func (g Gate) inScope(r *sarif.Result) bool {
	return len(g.Severities) == 0 || sarif.MatchesSeverity(r, g.Severities)
}

// ParseGateSeverities validates the --error-on-severity values and returns them in lowercase.
func ParseGateSeverities(values []string) ([]string, error) {
	var severities []string
	for _, value := range values {
		value = strings.TrimSpace(value)
		if err := sarif.ValidateSeverityFor("--error-on-severity", value); err != nil {
			return nil, err
		}
		severities = append(severities, strings.ToLower(value))
	}
	return severities, nil
}
