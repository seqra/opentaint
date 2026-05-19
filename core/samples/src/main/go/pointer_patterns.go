package test
import "test/util"


// ── Pointer aliasing and indirection pattern tests ───────────────────

type PPData struct {
	value string
	other string
}

// ── Pointer aliasing ─────────────────────────────────────────────────

func ptrAlias001T() {
	data := util.Source()
	p1 := &data
	p2 := p1
	util.Sink(*p2)
}

func ptrAlias002F() {
	data := util.Source()
	_ = &data
	safe := "clean"
	p2 := &safe
	util.Sink(*p2)
}

// ── Pointer to struct field ──────────────────────────────────────────

func ptrField001T() {
	data := util.Source()
	obj := &PPData{value: "clean", other: "clean"}
	obj.value = data
	util.Sink(obj.value)
}

func ptrField002F() {
	data := util.Source()
	obj := &PPData{value: "clean", other: "clean"}
	obj.value = data
	util.Sink(obj.other)
}

// ── Function writing through pointer parameter ──────────────────────

func writeThroughPtr(obj *PPData, val string) {
	obj.value = val
}

func readPPValue(obj *PPData) string {
	return obj.value
}

func readPPOther(obj *PPData) string {
	return obj.other
}

func ptrFunc001T() {
	data := util.Source()
	obj := &PPData{value: "clean", other: "clean"}
	writeThroughPtr(obj, data)
	result := readPPValue(obj)
	util.Sink(result)
}

func ptrFunc002F() {
	data := util.Source()
	obj := &PPData{value: "clean", other: "clean"}
	writeThroughPtr(obj, data)
	result := readPPOther(obj)
	util.Sink(result)
}

// ── Pointer dereference ──────────────────────────────────────────────

func ptrDeref001T() {
	data := util.Source()
	p := &data
	result := *p
	util.Sink(result)
}

func ptrDeref002F() {
	_ = util.Source()
	safe := "clean"
	p := &safe
	result := *p
	util.Sink(result)
}
