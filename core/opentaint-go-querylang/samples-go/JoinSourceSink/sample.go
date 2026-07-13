package util

func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

// Positive_join: tainted Source() result flows to Sink — the joined
// source/sink rule must report it.
func Positive_join() {
	s := Source()
	Sink(s)
}

// Negative_join: a constant reaches Sink, no taint — must stay clean.
func Negative_join() {
	Sink("safe")
}
