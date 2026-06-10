package util

func Positive_sliceReadElem(s []interface{}) {
	dst := s[0]
	// alias: arg0[]
	aliasSink(dst)
}

func Positive_sliceWriteRead(s []interface{}, src interface{}) {
	s[0] = src
	dst := s[0]
	// alias: arg1
	aliasSink(dst)
}

func Positive_sliceWriteReadMiddle(s []interface{}, src interface{}) {
	s[5] = src
	dst := s[5]
	// alias: arg1
	aliasSink(dst)
}

func Positive_mapReadElem(m map[string]interface{}) {
	dst := m["key"]
	// alias: arg0[]
	aliasSink(dst)
}

func Positive_mapWriteRead(m map[string]interface{}, src interface{}) {
	m["key"] = src
	dst := m["key"]
	// alias: arg1
	aliasSink(dst)
}

func Positive_mapWriteReadDiffKey(m map[string]interface{}, src interface{}) {
	m["a"] = src
	dst := m["b"]
	// alias: arg1
	aliasSink(dst)
}

func Positive_sliceOfBoxRead(s []*Box) {
	dst := s[0].value
	// alias: arg0[].value
	aliasSink(dst)
}

func Positive_sliceOfBoxWrite(s []*Box, src interface{}) {
	s[0].value = src
	dst := s[0].value
	// alias: arg1
	aliasSink(dst)
}

func Positive_mapOfBoxRead(m map[string]*Box) {
	dst := m["k"].value
	// alias: arg0[].value
	aliasSink(dst)
}

func Positive_mapOfBoxWrite(m map[string]*Box, src interface{}) {
	m["k"].value = src
	dst := m["k"].value
	// alias: arg1
	aliasSink(dst)
}

func Positive_sliceElemFieldPtr(s []*Box) {
	dst := s[0].value
	// alias: arg0[].value
	aliasSink(dst)
}

func Positive_sliceWriteElemFieldPtr(s []*Box, src interface{}) {
	s[0].value = src
	dst := s[0].value
	// alias: arg1
	aliasSink(dst)
}

func Positive_chanReceive(ch chan interface{}, src interface{}) {
	ch <- src
	dst := <-ch
	// alias: arg1
	aliasSink(dst)
}

func Positive_chanSendRead(ch chan interface{}) {
	dst := <-ch
	// alias: arg0[]
	aliasSink(dst)
}

func Positive_sliceCondWrite(s []interface{}, src interface{}, c bool) {
	if c {
		s[0] = src
	}
	dst := s[0]
	// alias: arg0[], arg1
	aliasSink(dst)
}

func Negative_sliceElemNotArg(s []interface{}, other interface{}) {
	dst := s[0]
	// alias: arg0[], !arg1
	aliasSink(dst)
}

func Negative_mapElemNotArg(m map[string]interface{}, other interface{}) {
	dst := m["k"]
	// alias: arg0[], !arg1
	aliasSink(dst)
}

func Positive_nestedSliceElem(s [][]interface{}) {
	dst := s[0]
	// alias: arg0[]
	aliasSink(dst)
}

func Positive_sliceWriteTwoElems(s []interface{}, src1, src2 interface{}) {
	s[0] = src1
	s[1] = src2
	dst := s[0]
	// alias: arg1, arg2
	aliasSink(dst)
}

func Positive_mapIntKey(m map[int]interface{}, src interface{}) {
	m[0] = src
	dst := m[0]
	// alias: arg1
	aliasSink(dst)
}

func Positive_sliceBoxElemSink(s []*Box, src interface{}) {
	s[0] = &Box{value: src}
	dst := s[0].value
	// alias: arg1
	aliasSink(dst)
}

func Positive_slicePassThrough(s []interface{}) {
	x := s[0]
	y := x
	// alias: arg0[]
	aliasSink(y)
}

func Positive_mapPassThrough(m map[string]interface{}) {
	x := m["k"]
	y := x
	// alias: arg0[]
	aliasSink(y)
}

func Negative_twoSlicesElemPrecision(s1, s2 []interface{}) {
	dst := s1[0]
	// alias: arg0[], !arg1[]
	aliasSink(dst)
}
