package util

type Outer struct {
	inner Pair
	tag   interface{}
}

func getPairA(p Pair) interface{} { return p.a }

func makePair(a interface{}) Pair { return Pair{a: a} }

func Positive_litAddressTaken(a, b interface{}) {
	p := Pair{a: a, b: b}
	q := &p
	dst := q.a
	// alias: arg0, !arg1
	aliasSink(dst)
}

func Positive_litUnkeyed(a, b interface{}) {
	p := Pair{a, b}
	dst := p.b
	// alias: arg1, !arg0
	aliasSink(dst)
}

func Positive_litPointer(a, b interface{}) {
	p := &Pair{a: a, b: b}
	dst := p.b
	// alias: arg1, !arg0
	aliasSink(dst)
}

func Positive_litAnonymousStruct(src interface{}) {
	s := struct{ v interface{} }{v: src}
	dst := s.v
	// alias: arg0
	aliasSink(dst)
}

func Positive_litZeroThenFieldWrite(src interface{}) {
	p := Pair{}
	p.a = src
	dst := p.a
	// alias: arg0
	aliasSink(dst)
}

func Negative_litZeroThenTwoWrites(a, b interface{}) {
	p := Pair{}
	p.a = a
	p.a = b
	dst := p.a
	// alias: arg1, !arg0
	aliasSink(dst)
}

func Negative_litTwoIndependent(a, b interface{}) {
	p := Pair{a: a}
	q := Pair{a: b}
	_ = q
	dst := p.a
	// alias: arg0, !arg1
	aliasSink(dst)
}

func Positive_litReassign(a, b interface{}) {
	p := Pair{a: a}
	p = Pair{a: b}
	dst := p.a
	// alias: arg1
	aliasSink(dst)
}

func Positive_litThroughPointer(p *Pair, src interface{}) {
	*p = Pair{a: src}
	dst := p.a
	// alias: arg0.a, arg1
	aliasSink(dst)
}

func Positive_litInLoop(s []interface{}) {
	var p Pair
	for i := 0; i < len(s); i++ {
		p = Pair{a: s[i]}
	}
	dst := p.a
	// alias: arg0[]
	aliasSink(dst)
}

func Positive_litInBranches(a, b interface{}, c bool) {
	var p Pair
	if c {
		p = Pair{a: a}
	} else {
		p = Pair{a: b}
	}
	dst := p.a
	// alias: arg0, arg1
	aliasSink(dst)
}

func Positive_litInMap(src interface{}) {
	m := map[string]Pair{"k": {a: src}}
	dst := m["k"].a
	// alias: arg0
	aliasSink(dst)
}

func Positive_litNestedValueTag(a, b interface{}) {
	o := Outer{inner: Pair{a: a}, tag: b}
	dst := o.tag
	// alias: arg1, !arg0
	aliasSink(dst)
}

func Positive_litNestedValue(a, b interface{}) {
	o := Outer{inner: Pair{a: a}, tag: b}
	dst := o.inner.a
	// engine alias: arg0, !arg1
	aliasSink(dst)
}

func Positive_litToField(o *Outer, src interface{}) {
	o.inner = Pair{a: src}
	dst := o.inner.a
	// engine alias: arg0.inner.a, arg1
	aliasSink(dst)
}

func Positive_litInSlice(a, b interface{}) {
	s := []Pair{{a: a}, {a: b}}
	dst := s[0].a
	// engine alias: arg0
	aliasSink(dst)
}

func Positive_litInArray(a, b interface{}) {
	arr := [2]Pair{{a: a}, {a: b}}
	dst := arr[0].a
	// engine alias: arg0
	aliasSink(dst)
}

func Positive_structCopy(a, b interface{}) {
	p := Pair{a: a, b: b}
	q := p
	dst := q.a
	// alias: arg0, !arg1
	aliasSink(dst)
}

func Positive_structCopyAddressTaken(a, b interface{}) {
	p := Pair{a: a}
	q := p
	r := &q
	r.b = b
	dst := q.a
	// alias: arg0, !arg1
	aliasSink(dst)
}

func Positive_structCopyThenWriteSource(a, b interface{}) {
	p := Pair{a: a}
	q := p
	p.a = b
	dst := q.a
	// alias: arg0
	aliasSink(dst)
}

func Positive_structCopyThenWriteCopy(a, b interface{}) {
	p := Pair{a: a}
	q := p
	q.a = b
	dst := p.a
	// alias: arg0
	aliasSink(dst)
}

func Positive_derefCopy(p *Pair) {
	v := *p
	dst := v.a
	// alias: arg0.a
	aliasSink(dst)
}

func Positive_derefCopyThenWritePointer(p *Pair, src interface{}) {
	v := *p
	p.a = src
	dst := v.a
	// alias: arg0.a
	aliasSink(dst)
}

func Positive_arrayLit(a, b interface{}) {
	arr := [2]interface{}{a, b}
	dst := arr[0]
	// alias: arg0
	aliasSink(dst)
}

func Positive_arrayLitAddressTaken(a, b interface{}) {
	arr := [2]interface{}{a, b}
	p := &arr
	dst := p[1]
	// alias: arg1
	aliasSink(dst)
}

func Positive_arrayLitZeroThenWrite(src interface{}) {
	arr := [2]interface{}{}
	arr[0] = src
	dst := arr[0]
	// alias: arg0
	aliasSink(dst)
}

func Positive_arrayCopy(a, b interface{}) {
	arr := [2]interface{}{a, b}
	c := arr
	dst := c[0]
	// alias: arg0
	aliasSink(dst)
}

func Positive_sliceLit(a, b interface{}) {
	s := []interface{}{a, b}
	dst := s[0]
	// alias: arg0
	aliasSink(dst)
}
