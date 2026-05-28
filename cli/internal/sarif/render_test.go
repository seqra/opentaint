package sarif

import (
	"bytes"
	"strings"
	"testing"

	"github.com/seqra/opentaint/internal/output"
)

func renderListing(t *testing.T, report *Report, opts ListingOptions) string {
	t.Helper()
	var buf bytes.Buffer
	p := output.NewWithWriter(&buf)
	report.PrintAll(p, opts)
	return buf.String()
}

func TestFingerprintAbbrev(t *testing.T) {
	r := makeResult("r", Error, "a.java", 1, map[string]string{
		DefaultFingerprintKey: "abcdefghijklmnopqrstuv",
	})
	if got := fingerprintAbbrev(&r, ""); got != "abcdefghijkl" { // 12 chars
		t.Errorf("fingerprintAbbrev = %q", got)
	}
	none := makeResult("r", Error, "a.java", 1, nil)
	if got := fingerprintAbbrev(&none, ""); got != "" {
		t.Errorf("expected empty abbrev, got %q", got)
	}
}

func TestPrintAllGroupsByRuleID(t *testing.T) {
	a := makeResult("alpha-rule", Error, "a.java", 1, nil)
	b1 := makeResult("beta-rule", Warning, "b.java", 2, nil)
	b2 := makeResult("beta-rule", Warning, "c.java", 3, nil)
	out := renderListing(t, makeReport(a, b1, b2), ListingOptions{GroupBy: groupByRuleID, MaxNestingLevel: -1})

	if !strings.Contains(out, "alpha-rule [1]") {
		t.Errorf("missing alpha-rule section header:\n%s", out)
	}
	if !strings.Contains(out, "beta-rule [2]") {
		t.Errorf("missing beta-rule section header:\n%s", out)
	}
	if strings.Index(out, "alpha-rule [1]") > strings.Index(out, "beta-rule [2]") {
		t.Error("expected alpha-rule section before beta-rule (lexicographic)")
	}
}

func TestPrintAllShowsFingerprint(t *testing.T) {
	r := makeResult("r", Error, "a.java", 1, map[string]string{DefaultFingerprintKey: "deadbeefcafe00"})
	out := renderListing(t, makeReport(r), ListingOptions{MaxNestingLevel: -1})
	if !strings.Contains(out, "deadbeefcafe") {
		t.Errorf("expected abbreviated fingerprint in listing:\n%s", out)
	}
}

func TestPrintAllSeverityGroupSortsByFile(t *testing.T) {
	// Two same-severity findings in different files: within the ERROR section they
	// must sort by file path (Alpha before Zeta) regardless of input order.
	z := makeResult("r-z", Error, "src/z/Zeta.java", 5, nil)
	a := makeResult("r-a", Error, "src/a/Alpha.java", 9, nil)
	out := renderListing(t, makeReport(z, a), ListingOptions{GroupBy: groupBySeverity, MaxNestingLevel: -1})

	if !strings.Contains(out, "ERROR [2]") {
		t.Fatalf("expected an ERROR [2] section:\n%s", out)
	}
	ia := strings.Index(out, "Alpha.java")
	iz := strings.Index(out, "Zeta.java")
	if ia < 0 || iz < 0 {
		t.Fatalf("expected both files in output:\n%s", out)
	}
	if ia > iz {
		t.Error("expected Alpha.java (file-sorted) before Zeta.java within the severity group")
	}
}

func TestPrintAllMultiFlowShowsCount(t *testing.T) {
	r := makeMultiFlowResult("r", Error, "a.java", 1, 3)
	out := renderListing(t, makeReport(r), ListingOptions{MaxNestingLevel: -1})
	if !strings.Contains(out, "Code flows: 3") {
		t.Errorf("expected 'Code flows: 3' field on multi-flow finding:\n%s", out)
	}
	if !strings.Contains(out, "Code flow (1 of 3)") {
		t.Errorf("expected '(1 of 3)' header by default:\n%s", out)
	}
}

func TestPrintAllSingleFlowNoCount(t *testing.T) {
	r := makeMultiFlowResult("r", Error, "a.java", 1, 1)
	out := renderListing(t, makeReport(r), ListingOptions{MaxNestingLevel: -1})
	if strings.Contains(out, "Code flows:") {
		t.Errorf("single-flow finding should not show 'Code flows:' field:\n%s", out)
	}
	if strings.Contains(out, "(1 of 1)") {
		t.Errorf("single-flow finding should not show '(1 of 1)' header:\n%s", out)
	}
	if !strings.Contains(out, "Code flow:") {
		t.Errorf("single-flow finding should keep plain 'Code flow:' header:\n%s", out)
	}
}

func TestPrintAllRendersAllCodeFlows(t *testing.T) {
	r := makeMultiFlowResult("r", Error, "a.java", 1, 2)
	out := renderListing(t, makeReport(r), ListingOptions{
		MaxNestingLevel: -1,
		CodeFlows:       CodeFlowSelection{All: true},
	})
	if !strings.Contains(out, "Code flow (1 of 2)") || !strings.Contains(out, "Code flow (2 of 2)") {
		t.Errorf("--code-flow all should render every flow:\n%s", out)
	}
}

func TestPrintAllRendersSpecificCodeFlow(t *testing.T) {
	r := makeMultiFlowResult("r", Error, "a.java", 1, 3)
	out := renderListing(t, makeReport(r), ListingOptions{
		MaxNestingLevel: -1,
		CodeFlows:       CodeFlowSelection{Index: 2},
	})
	if !strings.Contains(out, "Code flow (2 of 3)") {
		t.Errorf("--code-flow 2 should render the second flow:\n%s", out)
	}
	if strings.Contains(out, "Code flow (1 of 3)") || strings.Contains(out, "Code flow (3 of 3)") {
		t.Errorf("--code-flow 2 should NOT render other flows:\n%s", out)
	}
}

func TestPrintAllCodeFlowOutOfRangeSilentlySkips(t *testing.T) {
	r := makeMultiFlowResult("r", Error, "a.java", 1, 2)
	out := renderListing(t, makeReport(r), ListingOptions{
		MaxNestingLevel: -1,
		CodeFlows:       CodeFlowSelection{Index: 5},
	})
	if !strings.Contains(out, "Code flows: 2") {
		t.Errorf("count field should still appear when index is out of range:\n%s", out)
	}
	if strings.Contains(out, "Code flow (") {
		t.Errorf("no flow section should be rendered when index is out of range:\n%s", out)
	}
}

func TestPrintAllVerboseSnippetsBlankBetweenSteps(t *testing.T) {
	// Three flow steps under --verbose-flow --show-code-snippets should render
	// with N-1 blank lines inserted between consecutive steps; without snippets
	// (just --verbose-flow) the blanks must not appear.
	r := makeFlowResult("r", Error, "a.java", 1,
		makeStep(1, []string{"source"}, "m1"),
		makeStep(2, []string{"taint"}, "m2"),
		makeStep(3, []string{"sink"}, "m3"),
	)
	with := renderListing(t, makeReport(r), ListingOptions{
		ShowCodeSnippets: true,
		VerboseFlow:      true,
		MaxNestingLevel:  -1,
	})
	without := renderListing(t, makeReport(r), ListingOptions{
		VerboseFlow:     true,
		MaxNestingLevel: -1,
	})
	diff := strings.Count(with, "\n") - strings.Count(without, "\n")
	if diff != 2 {
		t.Errorf("expected 2 extra blank lines between 3 verbose+snippets steps, got diff=%d\nwith:\n%s\nwithout:\n%s", diff, with, without)
	}
}

func TestPrintAllNestingDropsHiddenPlaceholder(t *testing.T) {
	// Under --max-nesting-level the (N steps hidden) placeholder must NOT be
	// rendered (the omitted flag is still set internally so the verbose-flow
	// suggestion still fires).
	r := makeFlowResult("r", Error, "a.java", 1,
		makeStep(1, []string{"source"}, "main"),
		makeStep(2, []string{"call"}, "main"),
		makeStep(3, []string{"unknown"}, "helper"),
		makeStep(4, []string{"unknown"}, "helper"),
		makeStep(5, []string{"sink"}, "main"),
	)
	out := renderListing(t, makeReport(r), ListingOptions{MaxNestingLevel: 0})
	if strings.Contains(out, "hidden") {
		t.Errorf("expected no '(N steps hidden)' placeholder under --max-nesting-level:\n%s", out)
	}
}

func TestPrintAllNestingSnippetsBlankBetweenKeptSteps(t *testing.T) {
	// Under --max-nesting-level with --show-code-snippets, consecutive KEPT
	// steps should be separated by a blank line (matching the verbose+snippets
	// behavior in the legacy branch).
	r := makeFlowResult("r", Error, "a.java", 1,
		makeStep(1, []string{"source"}, "main"),
		makeStep(2, []string{"call"}, "main"),
		makeStep(3, []string{"unknown"}, "helper"),
		makeStep(4, []string{"sink"}, "main"),
	)
	with := renderListing(t, makeReport(r), ListingOptions{
		ShowCodeSnippets: true,
		MaxNestingLevel:  0, // hides the helper step at level 1; keeps source/call/sink
	})
	without := renderListing(t, makeReport(r), ListingOptions{MaxNestingLevel: 0})
	if strings.Count(with, "\n") <= strings.Count(without, "\n") {
		t.Errorf("expected extra blank lines under nesting+snippets:\nwith:\n%s\nwithout:\n%s", with, without)
	}
}

func TestPrintAllFingerprintHeaderHasRuleSubfield(t *testing.T) {
	// When a finding has a partial fingerprint, the finding's tree header is
	// "Fingerprint: <abbrev>" and the rule moves into a Rule: subfield.
	r := makeResult("my-rule", Error, "a.java", 1, map[string]string{
		DefaultFingerprintKey: "abc123def456ghi",
	})
	out := renderListing(t, makeReport(r), ListingOptions{MaxNestingLevel: -1})
	if !strings.Contains(out, "Fingerprint:") {
		t.Errorf("expected 'Fingerprint:' in header:\n%s", out)
	}
	if !strings.Contains(out, "abc123def456") {
		t.Errorf("expected abbreviated fingerprint in output:\n%s", out)
	}
	if !strings.Contains(out, "Rule:") {
		t.Errorf("expected 'Rule:' subfield when fingerprint header is used:\n%s", out)
	}
	if !strings.Contains(out, "my-rule") {
		t.Errorf("expected rule id in subtree:\n%s", out)
	}
}

func TestPrintAllNoFingerprintFallbackToRuleHeader(t *testing.T) {
	// When a finding has no fingerprint, the header stays the rule id and no
	// separate Rule: subfield is added (it would just duplicate the header).
	r := makeResult("my-rule", Error, "a.java", 1, nil)
	out := renderListing(t, makeReport(r), ListingOptions{MaxNestingLevel: -1})
	if !strings.Contains(out, "my-rule") {
		t.Errorf("expected rule id as header:\n%s", out)
	}
	if strings.Contains(out, "Rule:") {
		t.Errorf("did not expect 'Rule:' subfield when no fingerprint:\n%s", out)
	}
	if strings.Contains(out, "Fingerprint:") {
		t.Errorf("did not expect 'Fingerprint:' header when absent:\n%s", out)
	}
}
