package util

// Helpers used by the rule under test.
// Go port of example.RuleReturnNotInside. The Java rule combines a
// `pattern-inside` (method-signature) with a `pattern-not-inside`
// (sanitizer call before return). Recast as a call-based source/sink
// rule with a cleaner (`util.Sanitize`).
//
// Each entry point uses an inline chain so the sanitizer runs in the
// same function as the sink — the Go pipeline currently models
// cleaners locally and does not propagate "sanitized return value"
// across function boundaries the way the Java rule's pattern-not-inside
// does at the AST level.
func Source() string            { return "tainted" }
func Sanitize(s string) string  { return s }
func Sink(s string)             { _ = s }

// Positive_no_sanitize: chained source-derived value reaches sink without sanitizer.
func Positive_no_sanitize() {
	src := Source()
	ret := src
	Sink(ret)
}

// Negative_with_sanitize: sanitizer runs between source and sink.
func Negative_with_sanitize() {
	src := Source()
	ret := src
	cleaned := Sanitize(ret)
	Sink(cleaned)
}
