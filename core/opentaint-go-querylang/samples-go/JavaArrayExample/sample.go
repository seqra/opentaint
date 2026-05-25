package util

// Go port of example.ArrayExample. The Java rule scopes around `@EntryPoint`
// methods receiving a `String[]` and matches either `arraySink($PARAM)` or
// `otherElementSink($PARAM)`. Go has no Java annotations and slices behave
// differently from arrays; recast as source/sink with two pattern-either sinks.
// Element access (`d[0]`) is dropped because the Go pipeline does not
// propagate slice-element taint as the Java pipeline does for arrays.
func Source() []string             { return []string{"tainted"} }
func ArraySink(data []string)      { _ = data }
func OtherElementSink(data string) { _ = data }

func Positive_array() {
	d := Source()
	ArraySink(d)
}

func Negative_no_source() {
	ArraySink([]string{"safe"})
}
