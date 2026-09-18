package cmd

import (
	"fmt"

	"github.com/seqra/opentaint/internal/analyzer"
)

func analyzerExitCodeRows() string {
	rows := ""
	for _, code := range []int{analyzer.ExitException, analyzer.ExitOOM, analyzer.ExitTimeout, analyzer.ExitConfigError} {
		rows += fmt.Sprintf("\n  %-3d  %s", code, analyzer.ExitMessage(code))
	}
	return rows
}

func scanExitCodesHelp(completedLine string) string {
	return `Exit codes:
  0    ` + completedLine + `
  1    General failure (configuration or infrastructure error)` + analyzerExitCodeRows()
}

func testExitCodesHelp(passedLine string) string {
	return `Exit codes:
  0    ` + passedLine + `
  1    General failure (configuration or infrastructure error)
  2    One or more tests failed (false negatives, false positives, or skipped samples)` + analyzerExitCodeRows()
}
