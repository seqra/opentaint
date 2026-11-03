package cmd

import (
	"fmt"
	"strings"

	"github.com/seqra/opentaint/internal/analyzer"
)

// analyzerExitCodeRows lists the analyzer exit codes. exceptionNote, when set, follows the
// unhandled exception row.
func analyzerExitCodeRows(exceptionNote string) string {
	rows := ""
	for _, code := range []int{analyzer.ExitException, analyzer.ExitOOM, analyzer.ExitTimeout, analyzer.ExitConfigError} {
		rows += fmt.Sprintf("\n  %-3d  %s", code, capitalize(analyzer.ExitMessage(code)))
		if code == analyzer.ExitException && exceptionNote != "" {
			rows += " " + exceptionNote
		}
	}
	return rows
}

// capitalize upper-cases the first letter, so the analyzer rows match the rows above them.
func capitalize(s string) string {
	if s == "" {
		return s
	}
	return strings.ToUpper(s[:1]) + s[1:]
}

func scanExitCodesHelp(completedLine string) string {
	return `Exit codes:
  0    ` + completedLine + `
  1    General failure (configuration or infrastructure error)` + analyzerExitCodeRows("")
}

func testExitCodesHelp(passedLine string) string {
	return `Exit codes:
  0    ` + passedLine + `
  1    General failure (configuration or infrastructure error)
  2    One or more tests failed (false negatives, false positives, or skipped samples)` + analyzerExitCodeRows("(the analyzer log path is printed)")
}
