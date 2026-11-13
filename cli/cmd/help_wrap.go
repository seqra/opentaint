package cmd

import (
	"os"
	"strings"

	"github.com/seqra/opentaint/internal/output"
	"github.com/spf13/cobra"
	"github.com/spf13/pflag"
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

// usageTemplate is the default cobra usage template with three changes. A command group shows
// <command> in place of [command]: it does nothing without one. The commands, the flags, and the
// global flags start their descriptions in one column. The last line has the form of the line
// after a usage error.
const usageTemplate = `Usage:{{if .HasAvailableSubCommands}}
  {{.CommandPath}} <command>{{else if .Runnable}}
  {{.UseLine}}{{end}}{{if gt (len .Aliases) 0}}

Aliases:
  {{.NameAndAliases}}{{end}}{{if .HasExample}}

Examples:
{{.Example}}{{end}}{{$column := helpColumn .}}{{if .HasAvailableSubCommands}}

Available Commands:{{range .Commands}}{{if (or .IsAvailableCommand (eq .Name "help"))}}
{{commandRow .Name $column}}{{.Short}}{{end}}{{end}}{{end}}{{if .HasAvailableLocalFlags}}

Flags:
{{flagRows .LocalFlags $column}}{{end}}{{if .HasAvailableInheritedFlags}}

Global Flags:
{{flagRows .InheritedFlags $column}}{{end}}{{if .HasAvailableSubCommands}}

Run ` + "`{{.CommandPath}} <command> --help`" + ` for more information about a command{{end}}
`

func configureHelpWrap() {
	cobra.AddTemplateFunc("wrapHelp", func(text string) string {
		return wrapHelp(text, helpWidth())
	})
	cobra.AddTemplateFunc("helpColumn", helpColumn)
	cobra.AddTemplateFunc("commandRow", commandRow)
	cobra.AddTemplateFunc("flagRows", flagRows)
	rootCmd.SetHelpTemplate(helpTemplate)
	rootCmd.SetUsageTemplate(usageTemplate)
}

const (
	// commandIndent is the indent of a command row, as cobra indents it.
	commandIndent = "  "
	// flagNameWidth is the width of the indent and the shorthand that pflag puts before the
	// long name of a flag: "  -o, " or six spaces.
	flagNameWidth = 6
	// columnGap is the space between the longest name and its description, as pflag leaves it.
	columnGap = 3
)

// helpColumn returns the column where the descriptions start in the usage of cmd: after the
// longest name of its commands, its flags, and its global flags.
func helpColumn(cmd *cobra.Command) int {
	width := 0
	for _, sub := range cmd.Commands() {
		if sub.IsAvailableCommand() || sub.Name() == "help" {
			width = max(width, len(commandIndent)+len(sub.Name()))
		}
	}
	for _, flags := range []*pflag.FlagSet{cmd.LocalFlags(), cmd.InheritedFlags()} {
		flags.VisitAll(func(flag *pflag.Flag) {
			if name, _, ok := flagRow(flag); ok {
				width = max(width, len(name))
			}
		})
	}
	return width + columnGap
}

// commandRow returns the start of the row of a command: the name, padded to column.
func commandRow(name string, column int) string {
	return padRight(commandIndent+name, column)
}

// flagRows returns the rows of the flags, with the descriptions at column.
func flagRows(flags *pflag.FlagSet, column int) string {
	var rows []string
	flags.VisitAll(func(flag *pflag.Flag) {
		if name, description, ok := flagRow(flag); ok {
			rows = append(rows, strings.TrimRight(padRight(name, column)+description, " "))
		}
	})
	return strings.Join(rows, "\n")
}

// flagRow splits the row that pflag prints for flag into the name, with the shorthand and the
// value, and the description, with the default value. It reports false for a hidden flag.
func flagRow(flag *pflag.Flag) (name, description string, ok bool) {
	if flag.Hidden {
		return "", "", false
	}
	// In a set of one flag, pflag puts exactly columnGap spaces after the name.
	single := pflag.NewFlagSet("", pflag.ContinueOnError)
	single.AddFlag(flag)
	row := strings.TrimRight(single.FlagUsages(), "\n")
	gap := strings.Index(row[flagNameWidth:], strings.Repeat(" ", columnGap))
	if gap < 0 {
		return row, "", true
	}
	end := flagNameWidth + gap
	return row[:end], row[end+columnGap:], true
}

func padRight(text string, width int) string {
	if len(text) >= width {
		return text + " "
	}
	return text + strings.Repeat(" ", width-len(text))
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
