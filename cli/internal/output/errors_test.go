package output

import (
	"bytes"
	"errors"
	"fmt"
	"os"
	"testing"
)

func TestCausesSplitsFmtWrappersOnly(t *testing.T) {
	pathErr := &os.PathError{Op: "open", Path: "report.sarif", Err: errors.New("no such file or directory")}
	err := fmt.Errorf("failed to download analyzer: %w", fmt.Errorf("read checksums: %w", pathErr))

	got := Causes(err)

	want := []string{"failed to download analyzer", "read checksums", "open report.sarif: no such file or directory"}
	if fmt.Sprint(got) != fmt.Sprint(want) {
		t.Fatalf("Causes = %q, want %q", got, want)
	}
}

func TestCausesKeepsAWrapperWithTextAfterTheCause(t *testing.T) {
	err := fmt.Errorf("compile %w (build log: x.log)", errors.New("failed"))
	if got := Causes(err); len(got) != 1 || got[0] != err.Error() {
		t.Fatalf("Causes = %q", got)
	}
}

func TestPrinterErrorPrintsTheCausesUnderTheMessage(t *testing.T) {
	var buf bytes.Buffer
	p := NewWithWriter(&buf)
	p.Configure("never", false)

	p.Error("Failed to load the SARIF report", fmt.Errorf("read: %w", errors.New("line 1\nline 2")))

	want := "Error: Failed to load the SARIF report\n  read\n  line 1\n  line 2\n"
	if buf.String() != want {
		t.Fatalf("output = %q, want %q", buf.String(), want)
	}
}

func TestPrinterErrorErrUsesTheFirstCauseAsTheMessage(t *testing.T) {
	var buf bytes.Buffer
	p := NewWithWriter(&buf)
	p.Configure("never", false)

	p.ErrorErr(fmt.Errorf("invalid filter: %w", errors.New("unknown level")))

	if want := "Error: Invalid filter\n  unknown level\n"; buf.String() != want {
		t.Fatalf("output = %q, want %q", buf.String(), want)
	}
}

func TestPrinterWarnAddsThePrefix(t *testing.T) {
	var buf bytes.Buffer
	p := NewWithWriter(&buf)
	p.Configure("never", false)

	p.Warnf("Replacing %s", "x")

	if want := "Warning: Replacing x\n"; buf.String() != want {
		t.Fatalf("output = %q, want %q", buf.String(), want)
	}
}
