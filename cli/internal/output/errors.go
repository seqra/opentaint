package output

import (
	"errors"
	"fmt"
	"os"
	"reflect"
	"strings"
)

// causeIndent indents the causes under the message of an error.
const causeIndent = "  "

// Error prints `Error: <message>` and, under it, the causes from err, one on each line.
// err may be nil.
func (p *Printer) Error(message string, err error) {
	p.problem(p.theme.Error.Render("Error: "+message), Causes(err))
}

// Errorf prints `Error: <message>` with a formatted message and no causes.
func (p *Printer) Errorf(format string, a ...any) {
	p.Error(fmt.Sprintf(format, a...), nil)
}

// ErrorErr prints err as an error: its first cause, capitalized, is the message.
func (p *Printer) ErrorErr(err error) {
	causes := Causes(err)
	if len(causes) == 0 {
		return
	}
	p.problem(p.theme.Error.Render("Error: "+capitalize(causes[0])), causes[1:])
}

// Fatal prints the error as Error does and exits with code 1.
func (p *Printer) Fatal(message string, err error) {
	p.Error(message, err)
	os.Exit(1)
}

// Fatalf prints the error as Errorf does and exits with code 1.
func (p *Printer) Fatalf(format string, a ...any) {
	p.Errorf(format, a...)
	os.Exit(1)
}

// FatalErr prints err as ErrorErr does and exits with code 1.
func (p *Printer) FatalErr(err error) {
	p.ErrorErr(err)
	os.Exit(1)
}

// Warn prints `Warning: <message>`.
func (p *Printer) Warn(message string) {
	fmt.Fprintln(p.w, p.theme.Warning.Render("Warning: "+message)) //nolint:errcheck
}

// WarnDetails prints `Warning: <message>` and, under it, the details, one on each line.
func (p *Printer) WarnDetails(message string, details ...string) {
	p.problem(p.theme.Warning.Render("Warning: "+message), details)
}

// Warnf prints `Warning: <message>` with a formatted message.
func (p *Printer) Warnf(format string, a ...any) {
	p.Warn(fmt.Sprintf(format, a...))
}

func (p *Printer) problem(header string, causes []string) {
	fmt.Fprintln(p.w, header)             //nolint:errcheck
	fmt.Fprint(p.w, formatCauses(causes)) //nolint:errcheck
}

// FormatError returns err as ErrorErr prints it, without colors.
func FormatError(err error) string {
	causes := Causes(err)
	if len(causes) == 0 {
		return ""
	}
	return "Error: " + capitalize(causes[0]) + "\n" + formatCauses(causes[1:])
}

func formatCauses(causes []string) string {
	var b strings.Builder
	for _, cause := range causes {
		for _, line := range strings.Split(cause, "\n") {
			b.WriteString(causeIndent + line + "\n")
		}
	}
	return b.String()
}

// Causes splits err into its causes, from the outermost. A cause is the text that a
// fmt.Errorf wrapper adds in front of the error that it wraps. Other errors, such as an
// *fs.PathError, are kept whole: their parts are not sentences.
func Causes(err error) []string {
	var causes []string
	for err != nil {
		text := err.Error()
		next := errors.Unwrap(err)
		if next == nil || !isFmtWrapper(err) {
			causes = append(causes, text)
			break
		}
		own, ok := strings.CutSuffix(text, next.Error())
		if !ok {
			causes = append(causes, text)
			break
		}
		if own = strings.TrimRight(own, ": \n"); own != "" {
			causes = append(causes, own)
		}
		err = next
	}
	return causes
}

func isFmtWrapper(err error) bool {
	t := reflect.TypeOf(err)
	return t.Kind() == reflect.Pointer && t.Elem().PkgPath() == "fmt"
}

func capitalize(text string) string {
	return Humanize(errors.New(text))
}
