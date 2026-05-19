package test
import "test/util"


// ── Pointer and heap escape tests ────────────────────────────────────

// ── Basic pointer operations ─────────────────────────────────────────

func pointer001T() {
	data := util.Source()
	p := &data
	util.Sink(*p)
}

func pointer002F() {
	data := util.Source()
	_ = data
	safe := "safe"
	p := &safe
	util.Sink(*p)
}

// ── Heap-allocated struct via new ────────────────────────────────────

type HeapObj struct {
	value string
}

func heapNew001T() {
	data := util.Source()
	obj := new(HeapObj)
	obj.value = data
	util.Sink(obj.value)
}

func heapNew002F() {
	_ = util.Source()
	obj := new(HeapObj)
	obj.value = "safe"
	util.Sink(obj.value)
}

// ── Heap escape: struct returned from function ───────────────────────

func makeHeapObj(val1 string) *HeapObj {
	return &HeapObj{value: val1}
}

func heapEscape001T() {
	data := util.Source()
	obj := makeHeapObj(data)
	util.Sink(obj.value)
}

func heapEscape002F() {
	_ = util.Source()
	obj := makeHeapObj("safe")
	util.Sink(obj.value)
}

// ── Pointer passed to function ───────────────────────────────────────

func setPtrValue(obj *HeapObj, val1 string) {
	obj.value = val1
}

func ptrArg001T() {
	data := util.Source()
	obj := &HeapObj{}
	setPtrValue(obj, data)
	util.Sink(obj.value)
}

func ptrArg002F() {
	_ = util.Source()
	obj := &HeapObj{}
	setPtrValue(obj, "safe")
	util.Sink(obj.value)
}

// ── Pointer indirection (double pointer) ─────────────────────────────

func ptrToPtr001T() {
	data := util.Source()
	p := &data
	pp := &p
	util.Sink(**pp)
}

// ── Slice of pointers ────────────────────────────────────────────────

func sliceOfPtr001T() {
	data := util.Source()
	obj := &HeapObj{value: data}
	ptrs := []*HeapObj{obj}
	util.Sink(ptrs[0].value)
}

func sliceOfPtr002F() {
	_ = util.Source()
	obj := &HeapObj{value: "safe"}
	ptrs := []*HeapObj{obj}
	util.Sink(ptrs[0].value)
}

// ── Map of pointers ──────────────────────────────────────────────────

func mapOfPtr001T() {
	data := util.Source()
	obj := &HeapObj{value: data}
	m := map[string]*HeapObj{"key": obj}
	util.Sink(m["key"].value)
}

func mapOfPtr002F() {
	_ = util.Source()
	obj := &HeapObj{value: "safe"}
	m := map[string]*HeapObj{"key": obj}
	util.Sink(m["key"].value)
}
