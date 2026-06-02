package util

func Positive_localVarChain(src interface{}) {
	a := src
	b := a
	c := b
	// alias: arg0
	aliasSink(c)
}

func Positive_multipleAssign(src interface{}) {
	var a, b interface{}
	a = src
	b = a
	// alias: arg0
	aliasSink(b)
}

func Positive_typeAssert(src interface{}) {
	v, _ := src.(int)
	_ = v
	x := src
	// alias: arg0
	aliasSink(x)
}

func Positive_nilCheck(b *Box) {
	if b == nil {
		return
	}
	dst := b.value
	// alias: arg0.value
	aliasSink(dst)
}

func Positive_returnValue(b *Box) {
	dst := b.value
	// alias: arg0.value
	aliasSink(dst)
}

func Positive_multiSink(a, b interface{}) {
	// alias: arg0
	aliasSink(a)
	// alias: arg1
	aliasSink(b)
}

func Positive_boxLiteral(src interface{}) {
	b := Box{value: src}
	dst := b.value
	// alias: arg0
	aliasSink(dst)
}

func Positive_pairLiteral(a, b interface{}) {
	p := Pair{a: a, b: b}
	dst := p.a
	// alias: arg0
	aliasSink(dst)
}

func Positive_nestedLiteral(src interface{}) {
	b := &Box{value: src}
	n := Nested{box: b}
	dst := n.box.value
	// alias: arg0
	aliasSink(dst)
}

func Positive_makeSlice(src interface{}) {
	s := make([]interface{}, 1)
	s[0] = src
	dst := s[0]
	// alias: arg0
	aliasSink(dst)
}

func Positive_makeMap(src interface{}) {
	m := make(map[string]interface{})
	m["k"] = src
	dst := m["k"]
	// alias: arg0
	aliasSink(dst)
}

func Positive_switchMerge(a, b interface{}, n int) {
	var r interface{}
	switch n {
	case 0:
		r = a
	case 1:
		r = b
	default:
		r = a
	}
	// alias: arg0, arg1
	aliasSink(r)
}

func Positive_namedReturn(b *Box) {
	dst := b.value
	// alias: arg0.value
	aliasSink(dst)
}

func Negative_unusedArg(a, b interface{}) {
	r := a
	_ = b
	// alias: arg0, !arg1
	aliasSink(r)
}

func Positive_pairBLiteral(a, b interface{}) {
	p := Pair{a: a, b: b}
	dst := p.b
	// alias: arg1
	aliasSink(dst)
}

func Positive_sliceRangeElem(s []interface{}) {
	var last interface{}
	for i := 0; i < len(s); i++ {
		last = s[i]
	}
	// alias: arg0[]
	aliasSink(last)
}

func Positive_mapRangeElem(m map[string]interface{}) {
	var last interface{}
	for _, v := range m {
		last = v
	}
	// alias: arg0[]
	aliasSink(last)
}

func Positive_channelMake(src interface{}) {
	ch := make(chan interface{}, 1)
	ch <- src
	dst := <-ch
	// alias: arg0
	aliasSink(dst)
}

func Negative_boxLiteralOtherField(a, b interface{}) {
	p := Pair{a: a, b: b}
	dst := p.a
	// alias: arg0, !arg1
	aliasSink(dst)
}

func Positive_nodeDataChain(nd *Node) {
	v := nd.data
	w := v
	// alias: arg0.data
	aliasSink(w)
}

func Positive_deepCopy(n *Nested, src interface{}) {
	n.box.value = src
	v := n.box.value
	w := v
	// alias: arg0.box.value, arg1
	aliasSink(w)
}
