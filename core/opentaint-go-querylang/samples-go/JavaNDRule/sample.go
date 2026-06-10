package util

// Go port of example.NDRule. The Java rule is:
//   $A = src(); ...; $B = src(); ...; $C = pass($A, $B); ...; sink($C);
// which the Java solver expects to drive into a state-var. Recast in Go as the
// underlying taint flow: any source value reaching `pass` taints its return.
func Source() string                        { return "tainted" }
func Pass(a string, b string) string        { return a + b }
func Sink(s string)                         { _ = s }

// Positive_two_sources_one_sink: two source values flow through pass into sink.
func Positive_two_sources_one_sink() {
	a := Source()
	b := Source()
	c := Pass(a, b)
	Sink(c)
}

// Positive_indirect: two sources flow through nested helpers.
func Positive_indirect() {
	a := Source()
	b := Source()
	f1(a, b)
}

func f1(x string, y string) {
	c := Pass(x, y)
	f2(c)
}

func f2(c string) {
	Sink(c)
}
