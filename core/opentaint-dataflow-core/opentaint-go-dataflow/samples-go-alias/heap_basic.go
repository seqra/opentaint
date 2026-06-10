package util

func Positive_readArgField(b *Box) {
	dst := b.value
	// alias: arg0.value
	aliasSink(dst)
}

func Positive_writeThenReadField(b *Box, src interface{}) {
	b.value = src
	dst := b.value
	// alias: arg0.value, arg1
	aliasSink(dst)
}

func Positive_simpleCopy(a interface{}) {
	x := a
	// alias: arg0
	aliasSink(x)
}

func Positive_condMerge(a1, a2 interface{}, c bool) {
	var r interface{}
	if c {
		r = a1
	} else {
		r = a2
	}
	// alias: arg0, arg1
	aliasSink(r)
}

func Negative_unrelatedField(a, b *Box) {
	r := a.value
	// alias: arg0.value, !arg1.value
	aliasSink(r)
}
