package util

func Negative_twoArgsOnlyFirst(a, b interface{}) {
	r := a
	// alias: arg0, !arg1
	aliasSink(r)
}

func Negative_twoArgsOnlySecond(a, b interface{}) {
	r := b
	// alias: arg1, !arg0
	aliasSink(r)
}

func Negative_fieldOfWrongBox(a, b *Box) {
	dst := a.value
	// alias: arg0.value, !arg1.value
	aliasSink(dst)
}

func Negative_fieldBNotA(a, b *Box) {
	dst := b.value
	// alias: arg1.value, !arg0.value
	aliasSink(dst)
}

func Negative_writeBReadA(a, b *Box, src interface{}) {
	b.value = src
	dst := a.value
	// alias: arg0.value, !arg2, !arg1.value
	aliasSink(dst)
}

func Negative_writeAThenReadBField(a, b *Box, src interface{}) {
	a.value = src
	dst := b.value
	// alias: arg1.value, !arg2, !arg0.value
	aliasSink(dst)
}

func Negative_unwrittenField(b *Box, src interface{}) {
	dst := b.value
	// alias: arg0.value, !arg1
	aliasSink(dst)
}

func Negative_pairAFieldNotB(p *Pair, src interface{}) {
	p.a = src
	dst := p.a
	// alias: arg0.a, arg1, !arg0.b
	aliasSink(dst)
}

func Negative_pairBFieldNotA(p *Pair, src interface{}) {
	p.b = src
	dst := p.b
	// alias: arg0.b, arg1, !arg0.a
	aliasSink(dst)
}

func Negative_derefNotField(p *interface{}, b *Box) {
	dst := *p
	// alias: arg0@, !arg1.value
	aliasSink(dst)
}

func Negative_fieldNotDeref(b *Box, p *interface{}) {
	dst := b.value
	// alias: arg0.value, !arg1@
	aliasSink(dst)
}

func Negative_sliceElemNotField(s []interface{}, b *Box) {
	dst := s[0]
	// alias: arg0[], !arg1.value
	aliasSink(dst)
}

func Negative_fieldNotSliceElem(b *Box, s []interface{}) {
	dst := b.value
	// alias: arg0.value, !arg1[]
	aliasSink(dst)
}

func Negative_threeArgsOnlyFirst(a, b, c interface{}) {
	r := a
	// alias: arg0, !arg1, !arg2
	aliasSink(r)
}

func Negative_threeArgsOnlySecond(a, b, c interface{}) {
	r := b
	// alias: arg1, !arg0, !arg2
	aliasSink(r)
}

func Negative_threeArgsOnlyThird(a, b, c interface{}) {
	r := c
	// alias: arg2, !arg0, !arg1
	aliasSink(r)
}

func Negative_nodeDataNotNextData(nd *Node) {
	dst := nd.data
	// alias: arg0.data, !arg0.next.data
	aliasSink(dst)
}

func Negative_nestedBoxNotValue(n *Nested) {
	dst := n.box
	// alias: arg0.box, !arg0.box.value
	aliasSink(dst)
}

func Negative_argNotExternalResult(src interface{}) {
	r := external(src)
	// alias: !arg0
	aliasSink(r)
}

func Negative_twoMapsDifferentArgs(m1, m2 map[string]interface{}) {
	dst := m1["k"]
	// alias: arg0[], !arg1[]
	aliasSink(dst)
}

func Negative_twoSlicesDifferentArgs(s1, s2 []interface{}) {
	dst := s1[0]
	// alias: arg0[], !arg1[]
	aliasSink(dst)
}

func Negative_condMergeNotThird(a, b, other interface{}, c bool) {
	var r interface{}
	if c {
		r = a
	} else {
		r = b
	}
	// alias: arg0, arg1, !arg2
	aliasSink(r)
}

func Negative_nodeNextNotData(nd *Node) {
	dst := nd.next
	// alias: arg0.next, !arg0.data
	aliasSink(dst)
}

func Negative_pairSecondBoxNotFirst(p *Pair, a, b *Box) {
	dst := a.value
	// alias: arg1.value, !arg2.value
	aliasSink(dst)
}

func Negative_differentFieldsSameStruct(p *Pair, va, vb interface{}) {
	p.a = va
	dst := p.a
	// alias: arg0.a, arg1, !arg2
	aliasSink(dst)
}
