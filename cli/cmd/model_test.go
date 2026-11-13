package cmd

import (
	"testing"

	"github.com/spf13/cobra"
)

// The language has no default: a Java and a Go model project differ in the build, the
// dependencies, and the layout of the models.
func TestModelInitRequiresLanguage(t *testing.T) {
	flag := modelInitCmd.Flags().Lookup("language")
	if flag == nil {
		t.Fatal("model init has no --language flag")
	}
	if flag.DefValue != "" {
		t.Errorf("--language default = %q, want none", flag.DefValue)
	}
	if flag.Annotations[cobra.BashCompOneRequiredFlag] == nil {
		t.Error("--language is not required")
	}
}
