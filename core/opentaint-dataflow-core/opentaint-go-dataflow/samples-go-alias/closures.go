// depth: 1
package util

func Positive_closureCapture(src interface{}) {
	f := func() interface{} { return src }
	r := f()
	// alias: arg0
	aliasSink(r)
}

func Positive_closureCaptureBox(b *Box) {
	f := func() interface{} { return b.value }
	r := f()
	// alias: arg0.value
	aliasSink(r)
}

func Positive_closureCaptureWrite(b *Box, src interface{}) {
	f := func() { b.value = src }
	f()
	dst := b.value
	// alias: arg0.value, arg1
	aliasSink(dst)
}

func Positive_closureCaptureReturn(src interface{}) {
	f := makeReturner(src)
	r := f()
	// alias: arg0
	aliasSink(r)
}

func Negative_closureCaptureIdentityDepth1(src interface{}) {
	f := func() interface{} { return identity(src) }
	r := f()
	// alias: !arg0
	aliasSink(r)
}

func Positive_closureMultiCapture(a, b interface{}) {
	f := func() interface{} { return a }
	r := f()
	// alias: arg0
	aliasSink(r)
}

func Positive_closureTwoCaptures(a, b interface{}) {
	f := func(pick bool) interface{} {
		if pick {
			return a
		}
		return b
	}
	r := f(true)
	// alias: arg0, arg1
	aliasSink(r)
}

func Positive_closureBoxCapture(b *Box, src interface{}) {
	g := func() interface{} { return b.value }
	b.value = src
	r := g()
	// alias: arg0.value, arg1
	aliasSink(r)
}

func Positive_closureArgPassthrough(src interface{}) {
	f := func(x interface{}) interface{} { return x }
	r := f(src)
	// alias: arg0
	aliasSink(r)
}

func Positive_closureNestedCapture(n *Nested) {
	f := func() interface{} { return n.box.value }
	r := f()
	// alias: arg0.box.value
	aliasSink(r)
}

func Positive_closureSliceCapture(s []interface{}) {
	f := func() interface{} { return s[0] }
	r := f()
	// alias: arg0[]
	aliasSink(r)
}

func Positive_closureMapCapture(m map[string]interface{}) {
	f := func() interface{} { return m["k"] }
	r := f()
	// alias: arg0[]
	aliasSink(r)
}

func Positive_closureCondCapture(a, b interface{}, c bool) {
	var f func() interface{}
	if c {
		f = func() interface{} { return a }
	} else {
		f = func() interface{} { return b }
	}
	r := f()
	// alias: arg0, arg1
	aliasSink(r)
}

func Positive_closureReturned(src interface{}) {
	makeF := func() func() interface{} {
		return func() interface{} { return src }
	}
	f := makeF()
	r := f()
	// alias: arg0
	aliasSink(r)
}

func Positive_closurePairCapture(p *Pair) {
	f := func() interface{} { return p.a }
	r := f()
	// alias: arg0.a
	aliasSink(r)
}

func Positive_closureNodeCapture(nd *Node) {
	f := func() interface{} { return nd.data }
	r := f()
	// alias: arg0.data
	aliasSink(r)
}

func Positive_closureCaptureDeref(p *interface{}) {
	f := func() interface{} { return *p }
	r := f()
	// alias: arg0@
	aliasSink(r)
}

func Positive_makeReturnerField(b *Box) {
	f := makeReturner(b.value)
	r := f()
	// alias: arg0.value
	aliasSink(r)
}
