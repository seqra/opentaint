package util

func Positive_calArrayRead(arr []interface{}) {
	dst := arr[0]
	// alias: arg0[]
	aliasSink(dst)
}

func Positive_calArrayWriteRead(arr []interface{}, src interface{}) {
	arr[0] = src
	dst := arr[0]
	// alias: arg1
	aliasSink(dst)
}

func Positive_calDerefRead(p *interface{}) {
	dst := *p
	// alias: arg0@
	aliasSink(dst)
}

func Positive_calDeepField(n *Nested) {
	dst := n.box.value
	// alias: arg0.box.value
	aliasSink(dst)
}

func Positive_calMapWriteRead(m map[string]interface{}, src interface{}) {
	m["k"] = src
	dst := m["k"]
	// alias: arg1
	aliasSink(dst)
}

func Positive_calExternalReturn(src interface{}) {
	r := external(src)
	// alias: !arg0
	aliasSink(r)
}
