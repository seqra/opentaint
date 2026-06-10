package test
import "test/util"


// ── Additional struct operation tests ────────────────────────────────

// ── Struct copy semantics ────────────────────────────────────────────

type SOData struct {
	value string
	extra string
}

func structCopy001T() {
	data := util.Source()
	original := SOData{value: data, extra: "x"}
	copied := original
	util.Sink(copied.value)
}

func structCopy002F() {
	data := util.Source()
	original := SOData{value: data, extra: "x"}
	copied := original
	util.Sink(copied.extra)
}

func structCopy003T() {
	data := util.Source()
	original := SOData{value: data, extra: "x"}
	copied := original
	original.value = "safe" // mutating original doesn't affect copy
	util.Sink(copied.value)
}

// ── Struct as function argument (value semantics) ────────────────────

func readSOValue(d SOData) string { return d.value }
func readSOExtra(d SOData) string { return d.extra }

func structArg001T() {
	data := util.Source()
	d := SOData{value: data, extra: "x"}
	result := readSOValue(d)
	util.Sink(result)
}

func structArg002F() {
	data := util.Source()
	d := SOData{value: data, extra: "x"}
	result := readSOExtra(d)
	util.Sink(result)
}

// ── Struct returned from function ────────────────────────────────────

func makeSOData(val string) SOData {
	return SOData{value: val, extra: "x"}
}

func structReturn001T() {
	data := util.Source()
	d := makeSOData(data)
	util.Sink(d.value)
}

func structReturn002F() {
	data := util.Source()
	d := makeSOData(data)
	util.Sink(d.extra)
}

// ── Nested struct modification ───────────────────────────────────────

type SOOuter struct {
	inner SOData
	label string
}

func nestedStructMod001T() {
	data := util.Source()
	o := SOOuter{
		inner: SOData{value: data, extra: "x"},
		label: "y",
	}
	util.Sink(o.inner.value)
}

func nestedStructMod002F() {
	data := util.Source()
	o := SOOuter{
		inner: SOData{value: data, extra: "x"},
		label: "y",
	}
	util.Sink(o.label)
}

func nestedStructMod003F() {
	data := util.Source()
	o := SOOuter{
		inner: SOData{value: data, extra: "x"},
		label: "y",
	}
	util.Sink(o.inner.extra)
}

// ── Struct pointer field modification ────────────────────────────────

func structPtrField001T() {
	data := util.Source()
	d := &SOData{}
	d.value = data
	util.Sink(d.value)
}

func structPtrField002F() {
	data := util.Source()
	d := &SOData{}
	d.value = data
	util.Sink(d.extra)
}

// ── Struct with method modifying field ───────────────────────────────

type SOWithMethod struct {
	data string
}

func (s *SOWithMethod) Set(val string) { s.data = val }
func (s SOWithMethod) Get() string     { return s.data }

func structMethod001T() {
	data := util.Source()
	s := &SOWithMethod{}
	s.Set(data)
	result := s.Get()
	util.Sink(result)
}

func structMethod002F() {
	_ = util.Source()
	s := &SOWithMethod{}
	s.Set("safe")
	result := s.Get()
	util.Sink(result)
}

// ── Pattern 6: deep nested NAMED-field chain (4 levels) ──────────────
//
// Empirical engine status: PASS (resolved 2026-05-28).
// assertReachable("test.nestedNamedDeep001T") and the negative
// assertNotReachable("test.nestedNamedDeep002F") both pass.
//
// FULL per-instruction facts from `printFactsAt` (post-fix):
//   construction of o := DeepL4{...{v: data}}:
//   L186 [0:1]  local DeepL4  // o (%1)                 facts: var(0)![taint].$
//   L186 [0:2]  %2 = &%1.n1   (&o.n1)                   facts: ∅
//   L186 [0:3]  %3 = &%2.n1   (&o.n1.n1)                facts: ∅
//   L186 [0:4]  %4 = &%3.n1   (&o.n1.n1.n1)             facts: ∅
//   L186 [0:5]  %5 = &%4.v    (&o.n1.n1.n1.v)           facts: ∅
//   L186 [0:6]  *%5 = data    (store)                   facts: ∅
//   read of o.n1.n1.n1.v:
//   L187 [0:7]  %7 = &%1.n1   (&o.n1, fresh)            facts: var(1).n1.n1.n1.v![taint].$  <- fact on ROOT
//   L187 [0:8]  %8 = &%7.n1                             facts: var(7).n1.n1.v![taint].$
//   L187 [0:9]  %9 = &%8.n1                             facts: var(8).n1.v![taint].$
//   L187 [0:10] %10 = &%9.v                             facts: var(9).v![taint].$
//   L187 [0:11] %11 = *%10                              facts: var(10)![taint].$
//   L187 [0:12] util.Sink(%11)                          facts: var(11)![taint].$
//
// Fix: the store `*%5 = data` now walks the full address-of-field chain
// (%5 = &%4.v, %4 = &%3.n1, %3 = &%2.n1, %2 = &%1.n1) back to the ROOT
// object `o` (%1) via GoFlowFunctionUtils.resolveAddrChain, landing the
// fact on `o.n1.n1.n1.v` instead of stranding it on the intermediate
// temporary %4. The read side re-derives addresses fresh from %1 and now
// peels the chain incrementally to reach the sink. The symmetric backward
// store precondition (GoMethodSequentPrecondition.handleStore) mirrors the
// chain resolution so trace resolution reaches the sink.

type DeepL1 struct{ v string }
type DeepL2 struct{ n1 DeepL1 }
type DeepL3 struct{ n1 DeepL2 }
type DeepL4 struct{ n1 DeepL3 }

func nestedNamedDeep001T() {
	data := util.Source()
	o := DeepL4{n1: DeepL3{n1: DeepL2{n1: DeepL1{v: data}}}}
	util.Sink(o.n1.n1.n1.v)
}

func nestedNamedDeep002F() {
	data := util.Source()
	_ = data
	o := DeepL4{n1: DeepL3{n1: DeepL2{n1: DeepL1{v: "safe"}}}}
	util.Sink(o.n1.n1.n1.v)
}

// ── Cluster C: constructor builds a multi-level struct from tainted input ──

type CtorInner struct{ v string }
type CtorOuter struct{ inner CtorInner }

func NewCtorOuter(val string) CtorOuter {
	return CtorOuter{inner: CtorInner{v: val}}
}

func nestedStructConstructor001T() {
	data := util.Source()
	o := NewCtorOuter(data)
	util.Sink(o.inner.v)
}

func nestedStructConstructor002F() {
	data := util.Source()
	o := NewCtorOuter(data)
	_ = o
	util.Sink("safe")
}
