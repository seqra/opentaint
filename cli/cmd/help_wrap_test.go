package cmd

import (
	"bytes"
	"strings"
	"testing"

	"github.com/spf13/cobra"
)

func TestWrapHelpWrapsParagraphsAndKeepsIndentedLines(t *testing.T) {
	text := "Scan a Java or Kotlin project for vulnerabilities. The command detects the build system, builds the project, and analyzes it in one step.\n" +
		"\n" +
		"Arguments:\n" +
		"  [<source-path>]  Project root (default: the current directory, which is where the command runs from)"

	got := wrapHelp(text, 40)

	want := "Scan a Java or Kotlin project for\n" +
		"vulnerabilities. The command detects the\n" +
		"build system, builds the project, and\n" +
		"analyzes it in one step.\n" +
		"\n" +
		"Arguments:\n" +
		"  [<source-path>]  Project root (default: the current directory, which is where the command runs from)"
	if got != want {
		t.Fatalf("wrapHelp:\n%s\nwant:\n%s", got, want)
	}
}

func TestWrapHelpKeepsHyphenatedWordsWhole(t *testing.T) {
	if got := wrapHelp("Use the flag --project-model", 22); got != "Use the flag\n--project-model" {
		t.Fatalf("wrapHelp = %q", got)
	}
}

func TestWrapHelpKeepsALongWord(t *testing.T) {
	path := "/a/very/long/path/that/does/not/fit/in/the/width"
	if got := wrapHelp("See "+path, 20); got != "See\n"+path {
		t.Fatalf("wrapHelp = %q", got)
	}
}

func TestHelpWrapsLongAtMaxWidth(t *testing.T) {
	var buf bytes.Buffer
	scanCmd.SetOut(&buf)
	defer scanCmd.SetOut(nil)
	if err := scanCmd.Help(); err != nil {
		t.Fatal(err)
	}

	long, _, _ := strings.Cut(buf.String(), "\nUsage:")
	for _, line := range strings.Split(long, "\n") {
		if !strings.HasPrefix(line, " ") && len([]rune(line)) > maxHelpWidth {
			t.Errorf("help line is longer than %d: %q", maxHelpWidth, line)
		}
	}
}

func TestHelpEndsWithTheDocsLink(t *testing.T) {
	var buf bytes.Buffer
	modelCmd.SetOut(&buf)
	defer modelCmd.SetOut(nil)
	if err := modelCmd.Help(); err != nil {
		t.Fatal(err)
	}
	if want := "\n\nLearn more at " + docsURL + "\n"; !strings.HasSuffix(buf.String(), want) {
		t.Errorf("help ends with %q, want %q", buf.String()[max(0, buf.Len()-120):], want)
	}
}

// The commands, the flags, and the global flags start their descriptions in one column.
func TestUsageAlignsTheDescriptions(t *testing.T) {
	root := &cobra.Command{Use: "tool"}
	root.PersistentFlags().StringP("color", "c", "auto", "Color mode")
	group := &cobra.Command{Use: "group", Short: "Group"}
	group.AddCommand(&cobra.Command{Use: "a-long-subcommand", Short: "Sub", Run: func(*cobra.Command, []string) {}})
	group.Flags().StringArray("dependency", nil, "Library")
	root.AddCommand(group)
	root.SetUsageTemplate(usageTemplate)

	usage := group.UsageString()
	column := helpColumn(group)
	descriptions := map[string]string{"a-long-subcommand": "Sub", "--dependency": "Library", "--color": "Color mode"}
	for name, description := range descriptions {
		var row string
		for _, line := range strings.Split(usage, "\n") {
			if strings.Contains(line, name) {
				row = line
			}
		}
		if got := strings.Index(row, description); got != column {
			t.Errorf("%s: description at %d, want %d:\n%s", name, got, column, usage)
		}
	}
	if !strings.Contains(usage, "tool group <command>") || !strings.Contains(usage, "Run `tool group <command> --help`") {
		t.Errorf("usage of a group:\n%s", usage)
	}
}
