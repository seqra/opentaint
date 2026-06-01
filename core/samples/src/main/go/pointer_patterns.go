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

// ── Pattern 8: new(T) pointer chain with deref-write + alias + deref-read
//
// Empirical engine status: PASS.
// assertReachable("test.ptrNewWriteAliasRead001T") succeeds.
//
// Per-instruction facts from `printFactsAt`:
//   L96  [0:1]  new string  // p1                       facts: var(0)![taint].$
//   L100 [0:4]  *p1 (out := *p1)                        facts: var(2)![taint].$
//   L101 [0:5]  util.Sink(out)                          facts: var(4)![taint].$
//   L-1  [0:6]  return                                  facts: var(4)![taint].$
//
// The simple forward dataflow at the pointer-assignment + deref-read steps
// already propagates the fact rooted at the heap object through to `out`.
// No alias analysis needed. Sink fires.

func ptrNewWriteAliasRead001T() {
	data := util.Source()
	p1 := new(string)
	p2 := new(string)
	*p2 = data
	p1 = p2
	out := *p1
	util.Sink(out)
}

func ptrNewWriteAliasRead002F() {
	_ = util.Source()
	p1 := new(string)
	p2 := new(string)
	*p2 = "safe"
	p1 = p2
	out := *p1
	util.Sink(out)
}
