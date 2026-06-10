package util

func Positive_linkedListData(head *Node) {
	cur := head
	for cur.next != nil {
		cur = cur.next
	}
	dst := cur.data
	// alias: arg0.next.data, arg0.data
	aliasSink(dst)
}

func Positive_linkedListNext(head *Node) {
	cur := head
	for cur.next != nil {
		cur = cur.next
	}
	dst := cur.next
	// alias: arg0.next.next, arg0.next
	aliasSink(dst)
}

func Positive_phiMergeTwoVars(a, b interface{}, c bool) {
	var r interface{}
	if c {
		r = a
	} else {
		r = b
	}
	// alias: arg0, arg1
	aliasSink(r)
}

func Positive_phiMergeThreeVars(a, b, c interface{}, cond int) {
	var r interface{}
	switch cond {
	case 0:
		r = a
	case 1:
		r = b
	default:
		r = c
	}
	// alias: arg0, arg1, arg2
	aliasSink(r)
}

func Positive_loopAccumulateSlice(s []interface{}) {
	var last interface{}
	for i := 0; i < len(s); i++ {
		last = s[i]
	}
	// alias: arg0[]
	aliasSink(last)
}

func Positive_loopCopySlice(src, dst []interface{}) {
	for i := 0; i < len(src); i++ {
		dst[i] = src[i]
	}
	result := dst[0]
	// alias: arg0[], arg1[]
	aliasSink(result)
}

func Positive_loopBoxField(boxes []*Box) {
	var last interface{}
	for _, b := range boxes {
		last = b.value
	}
	// alias: arg0[].value
	aliasSink(last)
}

func Positive_loopNodeWrite(head *Node, src interface{}) {
	cur := head
	for cur != nil {
		cur.data = src
		cur = cur.next
	}
	dst := head.data
	// alias: arg0.data, arg1
	aliasSink(dst)
}

func Positive_loopSliceWriteRead(s []interface{}, src interface{}) {
	for i := range s {
		s[i] = src
	}
	dst := s[0]
	// alias: arg0[], arg1
	aliasSink(dst)
}

func Positive_phiBoxField(a, b *Box, c bool) {
	var r interface{}
	if c {
		r = a.value
	} else {
		r = b.value
	}
	// alias: arg0.value, arg1.value
	aliasSink(r)
}

func Positive_phiNestedField(n *Nested, b *Box, c bool) {
	var r interface{}
	if c {
		r = n.box.value
	} else {
		r = b.value
	}
	// alias: arg0.box.value, arg1.value
	aliasSink(r)
}

func Positive_loopPairFields(pairs []*Pair) {
	var last interface{}
	for _, p := range pairs {
		last = p.a
	}
	// alias: arg0[].a
	aliasSink(last)
}

func Positive_loopDeref(ptrs []*interface{}) {
	var last interface{}
	for _, p := range ptrs {
		last = *p
	}
	// alias: arg0[]@
	aliasSink(last)
}

func Positive_loopMapWrite(m map[string]interface{}, src interface{}) {
	for k := range m {
		m[k] = src
	}
	dst := m["a"]
	// alias: arg0[], arg1
	aliasSink(dst)
}

func Positive_phiDeref(p, q *interface{}, c bool) {
	var r *interface{}
	if c {
		r = p
	} else {
		r = q
	}
	dst := *r
	// alias: arg0@, arg1@
	aliasSink(dst)
}

func Positive_loopSliceToMap(s []interface{}, m map[int]interface{}) {
	for i, v := range s {
		m[i] = v
	}
	dst := m[0]
	// alias: arg0[], arg1[]
	aliasSink(dst)
}

func Positive_phiSliceMapElem(s []interface{}, m map[string]interface{}, c bool) {
	var r interface{}
	if c {
		r = s[0]
	} else {
		r = m["k"]
	}
	// alias: arg0[], arg1[]
	aliasSink(r)
}

func Negative_loopBodyNotOtherArg(s []interface{}, other interface{}) {
	var last interface{}
	for _, v := range s {
		last = v
	}
	// alias: arg0[], !arg1
	aliasSink(last)
}

func Positive_linkedListWriteData(head *Node, src interface{}) {
	cur := head
	for cur != nil {
		cur.data = src
		cur = cur.next
	}
	cur2 := head
	for cur2 != nil {
		cur2 = cur2.next
	}
	_ = cur2
	dst := head.next.data
	// alias: arg0.next.data, arg1
	aliasSink(dst)
}

func Positive_phiNodeData(a, b *Node, c bool) {
	var nd *Node
	if c {
		nd = a
	} else {
		nd = b
	}
	dst := nd.data
	// alias: arg0.data, arg1.data
	aliasSink(dst)
}

func Positive_loopWriteToField(boxes []*Box, src interface{}) {
	for _, b := range boxes {
		b.value = src
	}
	dst := boxes[0].value
	// alias: arg0[].value, arg1
	aliasSink(dst)
}

func Positive_loopAccumPair(pairs []*Pair) {
	var last interface{}
	for _, p := range pairs {
		last = p.b
	}
	// alias: arg0[].b
	aliasSink(last)
}
