package util

// Go port of example.TrickyPatterNot. Java rule disables matches where another
// variable was source-then-cleaned-then-reassigned-into-$SINK. The basic Go
// equivalent: source/clean/sink with the cleaner correctly dropping taint.
func Source() string         { return "tainted" }
func Clean(s string) string  { return s }
func Sink(s string)          { _ = s }

func Positive_simple() {
	r := method()
	Sink(r)
}

func method() string {
	s := Source()
	return s
}

func Negative_clean() {
	r := cleanedMethod()
	Sink(r)
}

func cleanedMethod() string {
	s := Source()
	return Clean(s)
}
