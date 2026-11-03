package cmd

import (
	"strings"

	"github.com/spf13/cobra"
	"github.com/spf13/pflag"
)

// deprecatedCommand returns a hidden copy of cmd under its old name. Running it prints that the
// name is deprecated, pointing at newPath, and then runs cmd with the same flags.
func deprecatedCommand(cmd *cobra.Command, oldName, newPath string) *cobra.Command {
	alias := &cobra.Command{
		Use:         oldName + strings.TrimPrefix(cmd.Use, cmd.Name()),
		Short:       cmd.Short,
		Long:        cmd.Long,
		Args:        cmd.Args,
		Run:         cmd.Run,
		Annotations: cmd.Annotations,
		Deprecated:  "use '" + newPath + "' instead",
	}
	alias.Flags().AddFlagSet(cmd.Flags())
	return alias
}

// deprecatedGroup returns a hidden command group under the old name of group. Its subcommands are
// deprecated too, so cobra lists none of them. The help of the old group is therefore the help of
// group, after the deprecation notice.
func deprecatedGroup(group *cobra.Command, oldName, newPath string) *cobra.Command {
	alias := &cobra.Command{
		Use:        oldName,
		Short:      group.Short,
		Deprecated: "use '" + newPath + "' instead",
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
	_ = flags.MarkDeprecated(oldName, "use --"+newName+" instead")
}
