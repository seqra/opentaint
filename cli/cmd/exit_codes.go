package cmd

import (
	"fmt"

	"github.com/seqra/opentaint/internal/analyzer"
)

// analyzerExitCodeRows renders the forwarded analyzer exit codes (252-255) as
// help rows. The row text is generated from analyzer.ExitMessage so the
// documented codes can never drift from the runtime failure messages.
func analyzerExitCodeRows() string {
	rows := ""
	for _, code := range []int{analyzer.ExitException, analyzer.ExitOOM, analyzer.ExitTimeout, analyzer.ExitConfigError} {
		rows += fmt.Sprintf("\n  %-3d  %s", code, analyzer.ExitMessage(code))
	}
	return rows
}

// scanExitCodesHelp renders the exit-codes block for commands that forward
// analyzer exit codes but have no failure gate (test rule reachability).
func scanExitCodesHelp(completedLine string) string {
	return `Exit codes:
  0    ` + completedLine + `
  1    General failure (configuration or infrastructure error)` + analyzerExitCodeRows()
}

// gateExitCodesHelp renders the exit-codes block for scan, which adds exit
// code 2 for the --error-on-findings gate on top of the forwarded analyzer
// codes.
func gateExitCodesHelp(completedLine string) string {
	return `Exit codes:
  0    ` + completedLine + `
  1    General failure (configuration or infrastructure error)
  2    Findings remain and --error-on-findings was set` + analyzerExitCodeRows()
}

// testExitCodesHelp renders the exit-codes block for the test-run commands,
// which add exit code 2 for sample failures.
func testExitCodesHelp(passedLine string) string {
	return `Exit codes:
  0    ` + passedLine + `
  1    General failure (configuration or infrastructure error)
  2    One or more tests failed (false negatives, false positives, or skipped samples)` + analyzerExitCodeRows()
}
