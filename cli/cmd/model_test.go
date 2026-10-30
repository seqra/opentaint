package cmd

import (
	"testing"

	"github.com/spf13/cobra"
)

func TestModelInitRequiresLanguage(t *testing.T) {
	flag := modelInitCmd.Flags().Lookup("language")
	if flag == nil {
		t.Fatal("model init has no language flag")
	}
	if flag.DefValue != "" {
		t.Fatalf("language default = %q, want no default", flag.DefValue)
	}
	if len(flag.Annotations[cobra.BashCompOneRequiredFlag]) == 0 {
		t.Fatal("language flag is not required")
	}
}
