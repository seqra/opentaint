package util

func Negative_depth0IdentityNoFlow(src interface{}) {
	r := identity(src)
	// alias: !arg0
	aliasSink(r)
}

func Negative_depth0GetterNoFlow(b *Box) {
	r := getValue(b)
	// alias: !arg0.value
	aliasSink(r)
}

func Negative_depth0WrapOnceNoFlow(src interface{}) {
	r := wrapOnce(src)
	// alias: !arg0
	aliasSink(r)
}

func Negative_depth0ExternalNoFlow(src interface{}) {
	r := external(src)
	// alias: !arg0
	aliasSink(r)
}

func Negative_depth0SetterNoGetterFlow(b *Box, src interface{}) {
	setValue(b, src)
	r := getValue(b)
	// alias: !arg1
	aliasSink(r)
}

func Negative_depth0IdentityOfField(b *Box) {
	r := identity(b.value)
	// alias: !arg0.value
	aliasSink(r)
}

func Negative_depth0MakeReturnerNoFlow(src interface{}) {
	f := makeReturner(src)
	r := f()
	// alias: !arg0
	aliasSink(r)
}

func Positive_depth0DirectCopy(src interface{}) {
	x := src
	// alias: arg0
	aliasSink(x)
}

func Positive_depth0FieldRead(b *Box) {
	dst := b.value
	// alias: arg0.value
	aliasSink(dst)
}

func Positive_depth0ArrayElem(s []interface{}) {
	dst := s[0]
	// alias: arg0[]
	aliasSink(dst)
}

func Positive_depth0FieldWrite(b *Box, src interface{}) {
	b.value = src
	dst := b.value
	// alias: arg0.value, arg1
	aliasSink(dst)
}

func Positive_depth0MapElem(m map[string]interface{}, src interface{}) {
	m["k"] = src
	dst := m["k"]
	// alias: arg1
	aliasSink(dst)
}

func Positive_depth0DerefRead(p *interface{}) {
	dst := *p
	// alias: arg0@
	aliasSink(dst)
}

func Positive_depth0CondMerge(a, b interface{}, c bool) {
	var r interface{}
	if c {
		r = a
	} else {
		r = b
	}
	// alias: arg0, arg1
	aliasSink(r)
}

func Negative_depth0ExternalTwoArgs(a, b interface{}) {
	r := external(a)
	// alias: !arg0, !arg1
	aliasSink(r)
}

func Positive_depth0NestedField(n *Nested) {
	dst := n.box.value
	// alias: arg0.box.value
	aliasSink(dst)
}

func Negative_depth0WrapOnceTwoArgs(a, b interface{}) {
	r := wrapOnce(a)
	// alias: !arg0, !arg1
	aliasSink(r)
}
