package util

// depth: 2

func Positive_twoHopIdentity(src interface{}) {
	r := wrapOnce(src)
	// alias: arg0
	aliasSink(r)
}

func Positive_twoHopField(b *Box) {
	r := getValueVia(b)
	// alias: arg0.value
	aliasSink(r)
}

func Positive_twoHopThenCopy(src interface{}) {
	r := wrapOnce(src)
	x := r
	// alias: arg0
	aliasSink(x)
}

func Positive_twoHopCondMerge(a1, a2 interface{}, c bool) {
	var s interface{}
	if c {
		s = a1
	} else {
		s = a2
	}
	r := wrapOnce(s)
	// alias: arg0, arg1
	aliasSink(r)
}

func Negative_threeHopExceedsDepth2(src interface{}) {
	r := wrapTwice(src)
	// alias: !arg0
	aliasSink(r)
}

func Negative_twoHopUnrelated(a, b interface{}) {
	r := wrapOnce(a)
	// alias: arg0, !arg1
	aliasSink(r)
}
