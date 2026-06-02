package util

func Positive_readPairA(p *Pair) {
	dst := p.a
	// alias: arg0.a
	aliasSink(dst)
}

func Positive_readPairB(p *Pair) {
	dst := p.b
	// alias: arg0.b
	aliasSink(dst)
}

func Positive_writePairAThenRead(p *Pair, src interface{}) {
	p.a = src
	dst := p.a
	// alias: arg0.a, arg1
	aliasSink(dst)
}

func Positive_writePairBThenRead(p *Pair, src interface{}) {
	p.b = src
	dst := p.b
	// alias: arg0.b, arg1
	aliasSink(dst)
}

func Positive_fieldCopyAtoB(p *Pair, src interface{}) {
	p.a = src
	p.b = p.a
	dst := p.b
	// alias: arg0.b, arg0.a, arg1
	aliasSink(dst)
}

func Positive_nestedBoxValue(n *Nested, src interface{}) {
	n.box.value = src
	dst := n.box.value
	// alias: arg0.box.value, arg1
	aliasSink(dst)
}

func Positive_readNestedBox(n *Nested) {
	dst := n.box
	// alias: arg0.box
	aliasSink(dst)
}

func Positive_nodeData(nd *Node) {
	dst := nd.data
	// alias: arg0.data
	aliasSink(dst)
}

func Positive_nodeNext(nd *Node) {
	dst := nd.next
	// alias: arg0.next
	aliasSink(dst)
}

func Positive_nodeNextData(nd *Node) {
	dst := nd.next.data
	// alias: arg0.next.data
	aliasSink(dst)
}

func Positive_writeNodeData(nd *Node, src interface{}) {
	nd.data = src
	dst := nd.data
	// alias: arg0.data, arg1
	aliasSink(dst)
}

func Positive_fieldToLocal(b *Box) {
	v := b.value
	x := v
	// alias: arg0.value
	aliasSink(x)
}

func Positive_twoFieldReads(b *Box, src interface{}) {
	b.value = src
	x := b.value
	// alias: arg0.value, arg1
	aliasSink(x)
	y := b.value
	// alias: arg0.value, arg1
	aliasSink(y)
}

func Positive_condFieldWrite(b *Box, src interface{}, c bool) {
	if c {
		b.value = src
	}
	dst := b.value
	// alias: arg0.value, arg1
	aliasSink(dst)
}

func Positive_condMergeFields(a, b *Box) {
	x := a.value
	y := b.value
	var r interface{}
	r = x
	_ = y
	// alias: arg0.value
	aliasSink(r)
}

func Negative_pairANotB(p *Pair) {
	dst := p.a
	// alias: arg0.a, !arg0.b
	aliasSink(dst)
}

func Negative_pairBNotA(p *Pair) {
	dst := p.b
	// alias: arg0.b, !arg0.a
	aliasSink(dst)
}

func Negative_twoBoxesFieldPrecision(a, b *Box) {
	dst := a.value
	// alias: arg0.value, !arg1.value
	aliasSink(dst)
}

func Negative_nodeDataNotNext(nd *Node) {
	dst := nd.data
	// alias: arg0.data, !arg0.next
	aliasSink(dst)
}

func Positive_swapPairFields(p *Pair, va, vb interface{}) {
	p.a = va
	p.b = vb
	tmp := p.a
	p.a = p.b
	dst := p.a
	// alias: arg0.a, arg0.b, arg2
	aliasSink(dst)
	_ = tmp
}

func Positive_copyBoxToNested(n *Nested, b *Box) {
	n.box = b
	dst := n.box
	// alias: arg0.box, arg1
	aliasSink(dst)
}

func Positive_nestedBoxThenValue(n *Nested, b *Box, src interface{}) {
	n.box = b
	b.value = src
	dst := n.box.value
	// alias: arg0.box.value, arg1.value, arg2
	aliasSink(dst)
}

func Positive_multiHopField(nd *Node, src interface{}) {
	nd.next.data = src
	dst := nd.next.data
	// alias: arg0.next.data, arg1
	aliasSink(dst)
}

func Positive_pairBothArgs(p *Pair, va, vb interface{}) {
	p.a = va
	p.b = vb
	da := p.a
	// alias: arg0.a, arg1
	aliasSink(da)
	db := p.b
	// alias: arg0.b, arg2
	aliasSink(db)
}

func Negative_differentArgFields(a, b *Box, src interface{}) {
	a.value = src
	dst := a.value
	// alias: arg0.value, arg2, !arg1.value
	aliasSink(dst)
}

func Positive_localBoxField(src interface{}) {
	b := &Box{}
	b.value = src
	dst := b.value
	// alias: arg0
	aliasSink(dst)
}

func Positive_nodeNextNext(nd *Node) {
	dst := nd.next.next
	// alias: arg0.next.next
	aliasSink(dst)
}
