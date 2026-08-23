package cmd

import (
	"os"
	"testing"

	"github.com/seqra/opentaint/internal/analyzer"
)

func withOSArgs(t *testing.T, args []string) {
	t.Helper()
	saved := os.Args
	os.Args = args
	t.Cleanup(func() { os.Args = saved })
}

func TestRerunWithoutDryRunStripsFlag(t *testing.T) {
	withOSArgs(t, []string{"/usr/bin/opentaint", "scan", "./proj", "--dry-run", "--color", "never"})
	got := rerunWithoutDryRun()
	want := "opentaint scan ./proj --color never"
	if got != want {
		t.Fatalf("rerunWithoutDryRun() = %q, want %q", got, want)
	}
}

func TestRerunWithoutDryRunStripsEqualsForm(t *testing.T) {
	withOSArgs(t, []string{"opentaint", "compile", ".", "--dry-run=true", "-o", "./model"})
	got := rerunWithoutDryRun()
	want := "opentaint compile . -o ./model"
	if got != want {
		t.Fatalf("rerunWithoutDryRun() = %q, want %q", got, want)
	}
}

func TestRerunWithoutDryRunQuotesSpaces(t *testing.T) {
	withOSArgs(t, []string{"opentaint", "scan", "my project", "--dry-run"})
	got := rerunWithoutDryRun()
	want := "opentaint scan 'my project'"
	if got != want {
		t.Fatalf("rerunWithoutDryRun() = %q, want %q", got, want)
	}
}

func TestWithFlag(t *testing.T) {
	if got := withFlag("opentaint prune", "--yes"); got != "opentaint prune --yes" {
		t.Fatalf("withFlag append = %q", got)
	}
	if got := withFlag("opentaint prune --yes", "--yes"); got != "opentaint prune --yes" {
		t.Fatalf("withFlag no-op = %q", got)
	}
}

func TestRerunReplacingFlagValueForm(t *testing.T) {
	withOSArgs(t, []string{"opentaint", "scan", ".", "--max-memory", "8G"})
	got := rerunReplacingFlag("16G", "--max-memory")
	want := "opentaint scan . --max-memory 16G"
	if got != want {
		t.Fatalf("rerunReplacingFlag() = %q, want %q", got, want)
	}
}

func TestRerunReplacingFlagAliasAndEqualsForm(t *testing.T) {
	withOSArgs(t, []string{"opentaint", "scan", ".", "-t", "15m", "--timeout=10m"})
	got := rerunReplacingFlag("30m0s", "--timeout", "-t")
	want := "opentaint scan . --timeout 30m0s"
	if got != want {
		t.Fatalf("rerunReplacingFlag() = %q, want %q", got, want)
	}
}

func TestRerunReplacingFlagAppendsWhenAbsent(t *testing.T) {
	withOSArgs(t, []string{"opentaint", "test", "rule", "run", "./model"})
	got := rerunReplacingFlag("16G", "--max-memory")
	want := "opentaint test rule run ./model --max-memory 16G"
	if got != want {
		t.Fatalf("rerunReplacingFlag() = %q, want %q", got, want)
	}
}

func TestDoubleMemory(t *testing.T) {
	cases := map[string]string{
		"8G":       "16G",
		"1024m":    "2048m",
		"83886080": "167772160",
		"weird":    "16G",
		"":         "16G",
	}
	for in, want := range cases {
		if got := doubleMemory(in); got != want {
			t.Fatalf("doubleMemory(%q) = %q, want %q", in, got, want)
		}
	}
}

func TestRetrySuggestion(t *testing.T) {
	withOSArgs(t, []string{"opentaint", "scan", ".", "--max-memory", "8G"})

	oom, ok := retrySuggestion(analyzer.ExitOOM, 900e9, "8G")
	if !ok || oom.Description != "To retry with more memory, run:" || oom.Command != "opentaint scan . --max-memory 16G" {
		t.Fatalf("OOM retry = %+v ok=%t", oom, ok)
	}

	timeoutRetry, ok := retrySuggestion(analyzer.ExitTimeout, 900e9, "8G")
	if !ok || timeoutRetry.Description != "To retry with a longer timeout, run:" {
		t.Fatalf("timeout retry = %+v ok=%t", timeoutRetry, ok)
	}
	want := "opentaint scan . --max-memory 8G --timeout 30m0s"
	if timeoutRetry.Command != want {
		t.Fatalf("timeout retry command = %q, want %q", timeoutRetry.Command, want)
	}

	if _, ok := retrySuggestion(analyzer.ExitException, 900e9, "8G"); ok {
		t.Fatal("exception exit code must not produce a retry suggestion")
	}
}
