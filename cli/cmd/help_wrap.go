package cmd

import (
	"os"
	"strings"

	"github.com/seqra/opentaint/internal/output"
	"github.com/spf13/cobra"
	"golang.org/x/term"
)

// maxHelpWidth is the widest that the help text is wrapped, even in a wider terminal.
const maxHelpWidth = 80

// docsURL is the documentation that the end of every help links to.
const docsURL = "https://github.com/seqra/opentaint/tree/main/docs"

// usageDocsURL is the page of the documentation on the commands. Next steps link to its sections.
const usageDocsURL = "https://github.com/seqra/opentaint/blob/main/docs/usage.md"

// helpTemplate is the default cobra help template with the Long text wrapped by wrapHelp and a
// link to the docs at the end.
const helpTemplate = `{{with (or .Long .Short)}}{{. | wrapHelp | trimTrailingWhitespaces}}

{{end}}{{if or .Runnable .HasSubCommands}}{{.UsageString}}
{{end}}Learn more at ` + docsURL + `
`

func configureHelpWrap() {
	cobra.AddTemplateFunc("wrapHelp", func(text string) string {
		return wrapHelp(text, helpWidth())
	})
	rootCmd.SetHelpTemplate(helpTemplate)
}

// helpWidth is the terminal width, at most maxHelpWidth. It is maxHelpWidth when stdout is not a terminal.
func helpWidth() int {
	fd := int(os.Stdout.Fd())
	if !term.IsTerminal(fd) {
		return maxHelpWidth
	}
	width, _, err := term.GetSize(fd)
	if err != nil || width <= 0 || width > maxHelpWidth {
		return maxHelpWidth
	}
	return width
}

// wrapHelp wraps the paragraph lines of a help text at width, at spaces only, so that flags and
// paths such as --project-model stay whole. Indented lines, such as the rows of the Arguments
// block, are kept as they are. A word longer than width is not split.
func wrapHelp(text string, width int) string {
	lines := strings.Split(text, "\n")
	for i, line := range lines {
		if strings.HasPrefix(line, " ") || strings.HasPrefix(line, "\t") {
			continue
		}
		lines[i] = output.WrapText(line, width)
	}
	return strings.Join(lines, "\n")
}
