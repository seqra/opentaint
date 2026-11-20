package cmd

import (
	"fmt"
	"strings"

	"github.com/spf13/cobra"
)

// requireKnownSubcommands makes cmd and every command group under it fail on an unknown
// subcommand. Cobra checks for one only in a root without Args, and a group with no Run of its own
// shows its help instead, with exit code 0. A group run with no subcommand still shows its help.
func requireKnownSubcommands(cmd *cobra.Command) {
	if cmd.HasSubCommands() {
		if cmd.Args == nil {
			cmd.Args = knownSubcommand
		}
		if !cmd.Runnable() {
			cmd.Run = func(c *cobra.Command, _ []string) {
				_ = c.Help()
			}
		}
	}
	for _, sub := range cmd.Commands() {
		requireKnownSubcommands(sub)
	}
}

// knownSubcommand is the Args of a command group. Cobra has already looked for a subcommand with
// the name of the first argument, so the argument names an unknown one.
func knownSubcommand(cmd *cobra.Command, args []string) error {
	if len(args) == 0 {
		return nil
	}
	return &unknownCommandError{group: cmd, name: args[0]}
}

// unknownCommandError is an argument of a command group that names none of its subcommands.
type unknownCommandError struct {
	group *cobra.Command
	name  string
}

func (e *unknownCommandError) Error() string {
	return fmt.Sprintf("unknown command `%s` for `%s`", e.name, e.group.CommandPath())
}

// suggestions returns the full paths of the subcommands that the user may have meant, as cobra
// finds them for a typo in the root.
func (e *unknownCommandError) suggestions() []string {
	if e.group.DisableSuggestions {
		return nil
	}
	if e.group.SuggestionsMinimumDistance <= 0 {
		e.group.SuggestionsMinimumDistance = 2
	}
	var commands []string
	for _, name := range e.group.SuggestionsFor(e.name) {
		commands = append(commands, "`"+e.group.CommandPath()+" "+name+"`")
	}
	return commands
}

// joinOr joins the items as a list in a sentence: "a", "a or b", "a, b, or c".
func joinOr(items []string) string {
	switch len(items) {
	case 0:
		return ""
	case 1:
		return items[0]
	case 2:
		return items[0] + " or " + items[1]
	}
	return strings.Join(items[:len(items)-1], ", ") + ", or " + items[len(items)-1]
}
