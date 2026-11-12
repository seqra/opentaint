package cmd

import (
	"maps"
	"strings"

	"github.com/spf13/cobra"
	"github.com/spf13/pflag"
)

// renamedTo annotates a hidden alias of a renamed command or flag with the new command path or
// flag name. The aliases are hidden instead of deprecated: cobra and pflag print their own
// deprecation notices, and these do not follow the style guide.
const renamedTo = "opentaint/renamed-to"

// deprecatedCommand returns a hidden copy of cmd under the last word of oldPath. Running it warns
// that oldPath is now newPath, and then runs cmd with the same flags.
func deprecatedCommand(cmd *cobra.Command, oldPath, newPath string) *cobra.Command {
	annotations := maps.Clone(cmd.Annotations)
	if annotations == nil {
		annotations = map[string]string{}
	}
	annotations[renamedTo] = newPath
	alias := &cobra.Command{
		Use:    lastWord(oldPath) + strings.TrimPrefix(cmd.Use, cmd.Name()),
		Short:  cmd.Short,
		Long:   cmd.Long,
		Hidden: true,
		// Cobra checks the arguments before the run hooks, which warn. An error in the arguments
		// comes with the warning too.
		Args: func(c *cobra.Command, args []string) error {
			if cmd.Args == nil {
				return nil
			}
			err := cmd.Args(c, args)
			if err != nil {
				warnRenamedCommand(c)
			}
			return err
		},
		Run:         cmd.Run,
		Annotations: annotations,
	}
	alias.Flags().AddFlagSet(cmd.Flags())
	return alias
}

// deprecatedGroup returns a hidden command group under the last word of oldPath. Its subcommands
// are hidden too, so help lists none of them. The help of the old group is therefore the help of
// group, after the warning.
func deprecatedGroup(group *cobra.Command, oldPath, newPath string) *cobra.Command {
	alias := &cobra.Command{
		Use:         lastWord(oldPath),
		Short:       group.Short,
		Hidden:      true,
		Annotations: map[string]string{renamedTo: newPath},
	}
	alias.SetHelpFunc(func(c *cobra.Command, args []string) {
		if c != alias {
			// The subcommands inherit this function. They keep the help of the root.
			c.Root().HelpFunc()(c, args)
			return
		}
		warnRenamedCommand(alias)
		_ = group.Help()
	})
	return alias
}

// renamedNotice tells that the command at oldPath is now at newPath.
func renamedNotice(oldPath, newPath string) string {
	return "`" + oldPath + "` is now `" + newPath + "`"
}

func lastWord(path string) string {
	return path[strings.LastIndex(path, " ")+1:]
}

// warnRenamedCommand warns when cmd is an alias of a renamed command.
func warnRenamedCommand(cmd *cobra.Command) {
	if newPath, ok := cmd.Annotations[renamedTo]; ok {
		out.Warn(renamedNotice(cmd.CommandPath(), newPath))
	}
}

// addDeprecatedFlagAlias registers oldName as a hidden alias of the flag newName. Both names set
// the same value, so they can be mixed on one command line.
func addDeprecatedFlagAlias(flags *pflag.FlagSet, newName, oldName string) {
	flag := flags.Lookup(newName)
	flags.AddFlag(&pflag.Flag{
		Name:        oldName,
		Usage:       flag.Usage,
		Value:       flag.Value,
		DefValue:    flag.DefValue,
		Hidden:      true,
		Annotations: map[string][]string{renamedTo: {newName}},
	})
}

// warnRenamedFlags warns about each alias of a renamed flag on the command line.
func warnRenamedFlags(cmd *cobra.Command) {
	cmd.Flags().Visit(func(flag *pflag.Flag) {
		if newName := flag.Annotations[renamedTo]; len(newName) > 0 {
			out.Warnf("--%s is now --%s", flag.Name, newName[0])
		}
	})
}

// isRenamedFlag reports whether flag is an alias of a renamed flag, which help never lists.
func isRenamedFlag(flag *pflag.Flag) bool {
	_, ok := flag.Annotations[renamedTo]
	return ok
}
