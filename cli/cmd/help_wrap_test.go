package cmd

import (
	"bytes"
	"strings"
	"testing"
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
