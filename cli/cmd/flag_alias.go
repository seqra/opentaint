package cmd

import (
	"strings"

	"github.com/spf13/pflag"
)

// renamedStringArray backs a renamed flag and its deprecated alias. pflag's
// stringArrayValue replaces the bound slice on each flag's own first value, so
// two stock flags bound to one slice silently drop whatever the other spelling
// already collected. Appending unconditionally keeps the values of both
// spellings, in command-line order.
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

// addRenamedStringArrayFlag registers a flag under its new name and its
// deprecated old spelling, both accumulating into the same slice.
func addRenamedStringArrayFlag(fs *pflag.FlagSet, target *[]string, name, deprecated, usage string) {
	fs.Var(renamedStringArray{target}, name, usage)
	fs.Var(renamedStringArray{target}, deprecated, usage)
	if err := fs.MarkDeprecated(deprecated, "use --"+name); err != nil {
		panic(err)
	}
}
