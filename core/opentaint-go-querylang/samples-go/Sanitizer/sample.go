package util

// Helpers used by the rule under test.
func Source() string         { return "tainted" }
func Sink(s string)          { _ = s }
func Clean(s string) string  { return s }

// Positive_unsanitized: tainted value reaches Sink without going through Clean.
func Positive_unsanitized() {
	Sink(Source())
}

// Negative_sanitized: tainted value is sanitized by Clean before reaching Sink.
func Negative_sanitized() {
	Sink(Clean(Source()))
}
