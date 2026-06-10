package util

type Box struct{ value interface{} }

type Pair struct {
	a interface{}
	b interface{}
}

type Nested struct{ box *Box }

type Node struct {
	next *Node
	data interface{}
}

func aliasSink(x interface{}) {}

func identity(x interface{}) interface{} { return x }

func getValue(b *Box) interface{} { return b.value }

func setValue(b *Box, v interface{}) { b.value = v }

func wrapOnce(x interface{}) interface{} { return identity(x) }

func wrapTwice(x interface{}) interface{} { return wrapOnce(x) }

func getValueVia(b *Box) interface{} { return getValue(b) }

func makeReturner(s interface{}) func() interface{} {
	return func() interface{} { return s }
}

func external(x interface{}) interface{}
