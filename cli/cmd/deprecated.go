package cmd

import (
	"strings"

	"github.com/spf13/cobra"
	"github.com/spf13/pflag"
)

// deprecatedCommand returns a hidden copy of cmd under the last word of oldPath. Running it prints
// that oldPath is now newPath, and then runs cmd with the same flags.
func deprecatedCommand(cmd *cobra.Command, oldPath, newPath string) *cobra.Command {
	oldName := lastWord(oldPath)
	alias := &cobra.Command{
		Use:         oldName + strings.TrimPrefix(cmd.Use, cmd.Name()),
		Short:       cmd.Short,
		Long:        cmd.Long,
		Args:        cmd.Args,
		Run:         cmd.Run,
		Annotations: cmd.Annotations,
		Deprecated:  renamedNotice(oldPath, newPath),
	}
	alias.Flags().AddFlagSet(cmd.Flags())
	return alias
}

// deprecatedGroup returns a hidden command group under the last word of oldPath. Its subcommands
// are deprecated too, so cobra lists none of them. The help of the old group is therefore the help
// of group, after the deprecation notice.
func deprecatedGroup(group *cobra.Command, oldPath, newPath string) *cobra.Command {
	alias := &cobra.Command{
		Use:        lastWord(oldPath),
		Short:      group.Short,
		Deprecated: renamedNotice(oldPath, newPath),
	}
	alias.SetHelpFunc(func(c *cobra.Command, args []string) {
		if c != alias {
			// The subcommands inherit this function. They keep the help of the root.
			c.Root().HelpFunc()(c, args)
			return
		}
		_ = group.Help()
	})
	return alias
}

// renamedNotice completes the cobra notice `Command "<name>" is deprecated, `. Cobra gives only
// the last word of the command, so the notice names both full paths.
func renamedNotice(oldPath, newPath string) string {
	return "`" + oldPath + "` is now `" + newPath + "`"
}

func lastWord(path string) string {
	return path[strings.LastIndex(path, " ")+1:]
}

// addDeprecatedFlagAlias registers oldName as a hidden, deprecated name of the flag newName.
// Both names set the same value, so they can be mixed on one command line.
func addDeprecatedFlagAlias(flags *pflag.FlagSet, newName, oldName string) {
	flag := flags.Lookup(newName)
	flags.AddFlag(&pflag.Flag{
		Name:     oldName,
		Usage:    flag.Usage,
		Value:    flag.Value,
		DefValue: flag.DefValue,
	})
	_ = flags.MarkDeprecated(oldName, "use `--"+newName+"` instead")
}
