package util

// Helpers used by the rule under test.
func Source() *string  { s := "tainted"; return &s }
func Sink(s *string)   { _ = s }
func IsNil(s *string) bool { return s == nil }

// Positive_unchecked: tainted value reaches Sink without a nil check.
func Positive_unchecked() {
	x := Source()
	Sink(x)
}

// Negative_checked: IsNil(x) sanitizes the taint before reaching Sink.
func Negative_checked() {
	x := Source()
	if !IsNil(x) {
		Sink(x)
	}
}
