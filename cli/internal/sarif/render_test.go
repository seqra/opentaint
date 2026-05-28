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
