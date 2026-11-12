//go:build !windows

package utils

import "testing"

func TestShellQuote(t *testing.T) {
	for in, want := range map[string]string{
		".opentaint/project":       ".opentaint/project",
		"sp ace/r.sarif":           "'sp ace/r.sarif'",
		"src/**":                   "'src/**'",
		"it's":                     `'it'\''s'`,
		"":                         "''",
		"<source-path>":            "<source-path>",
		"<group:artifact:version>": "<group:artifact:version>",
		"<not a placeholder>":      "'<not a placeholder>'",
	} {
		if got := ShellQuote(in); got != want {
			t.Errorf("ShellQuote(%q) = %q, want %q", in, got, want)
		}
	}
}
