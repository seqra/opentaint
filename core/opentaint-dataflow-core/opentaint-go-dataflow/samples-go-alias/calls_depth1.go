// depth: 1
package util

func Positive_identityFlows(src interface{}) {
	r := identity(src)
	// alias: arg0
	aliasSink(r)
}

func Positive_getterField(b *Box) {
	r := getValue(b)
	// alias: arg0.value
	aliasSink(r)
}

func Positive_setterThenGetter(b *Box, src interface{}) {
	setValue(b, src)
	r := getValue(b)
	// alias: arg0.value, arg1
	aliasSink(r)
}

func Positive_identityChain(src interface{}) {
	a := identity(src)
	r := identity(a)
	// alias: arg0
	aliasSink(r)
}

func Positive_identityThenField(b *Box) {
	v := getValue(b)
	r := identity(v)
	// alias: arg0.value
	aliasSink(r)
}

func Positive_setterGetterBox(b *Box, src interface{}) {
	setValue(b, src)
	r := b.value
	// alias: arg0.value, arg1
	aliasSink(r)
}

func Positive_identityOfField(b *Box) {
	r := identity(b.value)
	// alias: arg0.value
	aliasSink(r)
}

func Positive_getterAfterDirectWrite(b *Box, src interface{}) {
	b.value = src
	r := getValue(b)
	// alias: arg0.value, arg1
	aliasSink(r)
}

func Positive_identitySliceElem(s []interface{}) {
	r := identity(s[0])
	// alias: arg0[]
	aliasSink(r)
}

func Positive_identityDeref(p *interface{}) {
	r := identity(*p)
	// alias: arg0@
	aliasSink(r)
}

func Positive_setterGetterTwice(b *Box, src interface{}) {
	setValue(b, src)
	r1 := getValue(b)
	// alias: arg0.value, arg1
	aliasSink(r1)
	r2 := getValue(b)
	// alias: arg0.value, arg1
	aliasSink(r2)
}

func Positive_identityPairField(p *Pair) {
	r := identity(p.a)
	// alias: arg0.a
	aliasSink(r)
}

func Positive_makeReturnerThenCall(src interface{}) {
	f := makeReturner(src)
	r := f()
	// alias: arg0
	aliasSink(r)
}

func Positive_identityCondMerge(a, b interface{}, c bool) {
	var src interface{}
	if c {
		src = a
	} else {
		src = b
	}
	r := identity(src)
	// alias: arg0, arg1
	aliasSink(r)
}

func Positive_getterNestedBox(n *Nested) {
	r := getValue(n.box)
	// alias: arg0.box.value
	aliasSink(r)
}

func Positive_setterGetterNested(n *Nested, src interface{}) {
	setValue(n.box, src)
	r := getValue(n.box)
	// alias: arg0.box.value, arg1
	aliasSink(r)
}

func Negative_depth1WrapOnceNoFlow(src interface{}) {
	r := wrapOnce(src)
	// alias: !arg0
	aliasSink(r)
}

func Negative_depth1WrapOnceFieldNoFlow(b *Box) {
	r := wrapOnce(b.value)
	// alias: !arg0.value
	aliasSink(r)
}
