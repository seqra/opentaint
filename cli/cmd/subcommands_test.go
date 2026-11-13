package cmd

import (
	"errors"
	"strings"
	"testing"

	"github.com/spf13/cobra"
)

func TestUnknownSubcommand(t *testing.T) {
	requireKnownSubcommands(rootCmd)
	for _, tc := range []struct {
		args            []string
		wantError       string
		wantSuggestions []string
	}{
		{[]string{"test", "sosal"}, "unknown command `sosal` for `opentaint test`", nil},
		{[]string{"test", "rul"}, "unknown command `rul` for `opentaint test`", []string{"`opentaint test rule`"}},
		{[]string{"scna"}, "unknown command `scna` for `opentaint`", []string{"`opentaint scan`"}},
		{[]string{"test", "rule", "ini"}, "unknown command `ini` for `opentaint test rule`", []string{"`opentaint test rule init`"}},
	} {
		t.Run(strings.Join(tc.args, " "), func(t *testing.T) {
			cmd, rest, err := rootCmd.Find(tc.args)
			if err != nil {
				t.Fatalf("Find: %v", err)
			}
			err = cmd.ValidateArgs(rest)
			var unknown *unknownCommandError
			if !errors.As(err, &unknown) {
				t.Fatalf("error = %v, want an unknown command", err)
			}
			if err.Error() != tc.wantError {
				t.Errorf("error = %q, want %q", err, tc.wantError)
			}
			if got := unknown.suggestions(); strings.Join(got, ",") != strings.Join(tc.wantSuggestions, ",") {
				t.Errorf("suggestions = %v, want %v", got, tc.wantSuggestions)
			}
		})
	}
}

// A group run with no subcommand shows its help, so it must be runnable for cobra to check
// its arguments.
func TestCommandGroupsCheckTheirSubcommand(t *testing.T) {
	requireKnownSubcommands(rootCmd)
	var visit func(cmd *cobra.Command)
	visit = func(cmd *cobra.Command) {
		if cmd.HasSubCommands() && (!cmd.Runnable() || cmd.Args == nil) {
			t.Errorf("%s does not check its subcommand", cmd.CommandPath())
		}
		for _, sub := range cmd.Commands() {
			visit(sub)
		}
	}
	visit(rootCmd)
}

func TestJoinOr(t *testing.T) {
	for _, tc := range []struct {
		items []string
		want  string
	}{
		{nil, ""},
		{[]string{"a"}, "a"},
		{[]string{"a", "b"}, "a or b"},
		{[]string{"a", "b", "c"}, "a, b, or c"},
	} {
		if got := joinOr(tc.items); got != tc.want {
			t.Errorf("joinOr(%v) = %q, want %q", tc.items, got, tc.want)
		}
	}
}
