package cmd

import (
	"strings"

	"github.com/spf13/pflag"
)

type renamedStringArray struct {
	target *[]string
}

func (v renamedStringArray) String() string {
	if len(*v.target) == 0 {
		return ""
	}
	return "[" + strings.Join(*v.target, ",") + "]"
}

func (v renamedStringArray) Set(s string) error {
	*v.target = append(*v.target, s)
	return nil
}

func (v renamedStringArray) Type() string {
	return "stringArray"
}

func addRenamedStringArrayFlag(fs *pflag.FlagSet, target *[]string, name, deprecated, usage string) {
	fs.Var(renamedStringArray{target}, name, usage)
	fs.Var(renamedStringArray{target}, deprecated, usage)
	if err := fs.MarkDeprecated(deprecated, "use --"+name); err != nil {
		panic(err)
	}
}
