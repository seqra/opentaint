// depth: 1
package util

func Positive_litPassedByValue(src interface{}) {
	dst := getPairA(Pair{a: src})
	// alias: arg0
	aliasSink(dst)
}

func Positive_litReturnedByValue(src interface{}) {
	p := makePair(src)
	dst := p.a
	// alias: arg0
	aliasSink(dst)
}

func Positive_litCapturedByClosure(src interface{}) {
	p := Pair{a: src}
	f := func() interface{} { return p.a }
	dst := f()
	// alias: arg0
	aliasSink(dst)
}
