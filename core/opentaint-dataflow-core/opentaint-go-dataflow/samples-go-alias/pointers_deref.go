package util

func Positive_derefPointer(p *interface{}) {
	dst := *p
	// alias: arg0@
	aliasSink(dst)
}

func Positive_writeDerefRead(p *interface{}, src interface{}) {
	*p = src
	dst := *p
	// alias: arg0@, arg1
	aliasSink(dst)
}

func Positive_pointerCopy(p *interface{}) {
	q := p
	dst := *q
	// alias: arg0@
	aliasSink(dst)
}

func Positive_addressOfLocal(src interface{}) {
	x := src
	p := &x
	dst := *p
	// alias: arg0
	aliasSink(dst)
}

func Positive_addressOfField(b *Box) {
	p := &b.value
	dst := *p
	// alias: arg0.value
	aliasSink(dst)
}

func Positive_addressOfFieldWrite(b *Box, src interface{}) {
	p := &b.value
	*p = src
	dst := b.value
	// alias: arg0.value, arg1
	aliasSink(dst)
}

func Positive_doublePointer(pp **interface{}) {
	dst := **pp
	// alias: arg0@@
	aliasSink(dst)
}

func Positive_doublePointerDerefOne(pp **interface{}) {
	dst := *pp
	// alias: arg0@
	aliasSink(dst)
}

func Positive_derefThenField(p *Box) {
	dst := p.value
	// alias: arg0.value
	aliasSink(dst)
}

func Positive_derefBoxPointer(pp **Box) {
	b := *pp
	dst := b.value
	// alias: arg0@.value
	aliasSink(dst)
}

func Positive_pointerFieldWrite(pp **Box, src interface{}) {
	(*pp).value = src
	dst := (*pp).value
	// alias: arg0@.value, arg1
	aliasSink(dst)
}

func Positive_addressOfSliceElem(s []interface{}) {
	p := &s[0]
	dst := *p
	// alias: arg0[]
	aliasSink(dst)
}

func Positive_condDerefRead(p *interface{}, src interface{}, c bool) {
	if c {
		*p = src
	}
	dst := *p
	// alias: arg0@, arg1
	aliasSink(dst)
}

func Negative_twoPointersDerefPrecision(p, q *interface{}) {
	dst := *p
	// alias: arg0@, !arg1@
	aliasSink(dst)
}

func Negative_derefNotArg(p *interface{}, other interface{}) {
	dst := *p
	// alias: arg0@, !arg1
	aliasSink(dst)
}

func Positive_pointerPassThrough(p *interface{}) {
	q := p
	r := q
	dst := *r
	// alias: arg0@
	aliasSink(dst)
}

func Positive_writePointerThenSink(src interface{}) {
	p := &src
	dst := *p
	// alias: arg0
	aliasSink(dst)
}

func Positive_nestedPointerField(n *Nested) {
	p := &n.box
	b := *p
	dst := b.value
	// alias: arg0.box.value
	aliasSink(dst)
}

func Positive_addressLocalThenWrite(src interface{}) {
	var x interface{}
	p := &x
	*p = src
	dst := x
	// alias: arg0
	aliasSink(dst)
}

func Positive_pointerCondMerge(p, q *interface{}) {
	var r *interface{}
	r = p
	_ = q
	dst := *r
	// alias: arg0@
	aliasSink(dst)
}

func Positive_fieldPointerDeref(b *Box, src interface{}) {
	p := &b.value
	*p = src
	dst := *p
	// alias: arg0.value, arg1
	aliasSink(dst)
}

func Negative_pointerNotUnrelatedField(p *interface{}, b *Box) {
	dst := *p
	// alias: arg0@, !arg1.value
	aliasSink(dst)
}
