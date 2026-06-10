package test
import "test/util"


// ── Type operation tests (casts, assertions, conversions, interface wrapping) ──

// ── Type conversion (preserves taint) ────────────────────────────────

func typeCastInt001T() {
	data := util.SourceInt()
	result := float64(data)
	util.SinkFloat(result)
}

func typeCastInt002F() {
	_ = util.SourceInt()
	result := float64(42)
	util.SinkFloat(result)
}

func typeCastStringToBytes001T() {
	data := util.Source()
	bytes := []byte(data)
	result := string(bytes)
	util.Sink(result)
}

func typeCastStringToBytes002F() {
	_ = util.Source()
	bytes := []byte("safe")
	result := string(bytes)
	util.Sink(result)
}

// ── Interface wrapping (MakeInterface preserves taint) ───────────────

func interfaceWrap001T() {
	data := util.Source()
	var iface interface{} = data
	result := iface.(string)
	util.Sink(result)
}

func interfaceWrap002F() {
	_ = util.Source()
	var iface interface{} = "safe"
	result := iface.(string)
	util.Sink(result)
}

// ── Type assertion ───────────────────────────────────────────────────

func typeAssert001T() {
	data := util.SourceAny()
	result := data.(string)
	util.Sink(result)
}

func typeAssert002F() {
	_ = util.SourceAny()
	var clean interface{} = "safe"
	result := clean.(string)
	util.Sink(result)
}

// ── Type assertion with comma-ok ─────────────────────────────────────

func typeAssertOk001T() {
	data := util.SourceAny()
	result, ok := data.(string)
	if ok {
		util.Sink(result)
	}
}

func typeAssertOk002F() {
	_ = util.SourceAny()
	var clean interface{} = "safe"
	result, ok := clean.(string)
	if ok {
		util.Sink(result)
	}
}

// ── Rune/byte conversion ─────────────────────────────────────────────

func runeConv001T() {
	data := util.SourceInt()
	r := rune(data)
	result := string(r)
	util.Sink(result)
}

func runeConv002F() {
	_ = util.SourceInt()
	r := rune(65)
	result := string(r)
	util.Sink(result)
}

// ── Pattern 4: type-assert on chained expression ─────────────────────
//
// Empirical engine status: ALL THREE variants PASS today.
//
// typeAssertOnMapElem001T facts:
//   L105 [0:1]  make map[string]interface{}(1)          facts: var(0)![taint].$
//   L105 [0:3]  m["k"] = data                           facts: var(2)![taint].$
//   L106 [0:4]  m["k"]                                  facts: var(1)[*]![taint].$
//   L106 [0:5]  result.(string)                         facts: var(4)![taint].$
//   L107 [0:6]  util.Sink(s)                            facts: var(5)![taint].$
//   The map-element fact (var(1)[*]) survives the index read; the assert
//   produces var(4); var(5) carries it to Sink.
//
// typeAssertOnFieldRead001T facts:
//   L121 [0:1]  local taIfaceBox  // b                  facts: var(0)![taint].$
//   L121 [0:4]  *b = composite                          facts: var(3)![taint].$
//   L122 [0:5]  &b.iface                                facts: var(1).iface![taint].$
//   L122 [0:6]  *&b.iface                               facts: var(5)![taint].$
//   L122 [0:7]  result.(string)                         facts: var(6)![taint].$
//   L123 [0:8]  util.Sink(s)                            facts: var(7)![taint].$
//
// typeAssertOnCallResult001T facts:
//   L-1  [0:1]  makeinterface(data)                     facts: var(0)![taint].$
//   L137 [0:2]  taIdentityIface(iface)                  facts: var(1)![taint].$
//   L137 [0:3]  result.(string)                         facts: var(1)![taint].$, var(2)![taint].$
//   L138 [0:4]  util.Sink(s)                            facts: var(3)![taint].$
//
// In every variant the type-assert site emits a fresh fact on its result
// when any fact reaches the operand. No engine work needed.

func typeAssertOnMapElem001T() {
	data := util.Source()
	m := map[string]interface{}{"k": data}
	s := m["k"].(string)
	util.Sink(s)
}

func typeAssertOnMapElem002F() {
	_ = util.Source()
	m := map[string]interface{}{"k": "safe"}
	s := m["k"].(string)
	util.Sink(s)
}

type taIfaceBox struct{ iface interface{} }

func typeAssertOnFieldRead001T() {
	data := util.Source()
	b := taIfaceBox{iface: data}
	s := b.iface.(string)
	util.Sink(s)
}

func typeAssertOnFieldRead002F() {
	_ = util.Source()
	b := taIfaceBox{iface: "safe"}
	s := b.iface.(string)
	util.Sink(s)
}

func taIdentityIface(x interface{}) interface{} { return x }

func typeAssertOnCallResult001T() {
	data := util.Source()
	s := taIdentityIface(data).(string)
	util.Sink(s)
}

func typeAssertOnCallResult002F() {
	_ = util.Source()
	s := taIdentityIface("safe").(string)
	util.Sink(s)
}

// ── Pattern 5: type-switch case binding merged via SSA phi ───────────
//
// Empirical engine status: PASS (resolved 2026-05-28).
// assertReachable("test.typeSwitchBinding001T") succeeds.
//
// FULL per-instruction forward-fact trace from `printFactsAt`:
//   L201 [0:0]  Source()                                facts: ∅
//   L-1  [0:1]  makeinterface(obj)                      facts: var(0)![taint].$
//   L204 [0:2]  obj.(string),ok                         facts: var(1)![taint].$
//   L-1  [0:3]  extract #0  (the binding `v`)           facts: var(2).$0![taint].$  <- value slot tainted
//   L-1  [0:4]  extract #1  (the `ok` bool)             facts: var(3)![taint].$     <- v survives
//   L-1  [0:5]  if (ok) then inst#9 else inst#6         facts: ∅
//   L202 [1:6]  phi(5: "safe", 9: %3:t3)  // dir        facts: ∅
//   L207 [1:7]  util.Sink(dir)                          facts: var(6)![taint].$     <- reaches sink
//   L-1  [1:8]  return                                  facts: var(6)![taint].$
//   L-1  [2:9]  jump inst#6                             facts: ∅
//
// Root cause and fix: the comma-ok type-assert `obj.(string),ok` produces a
// (value, ok) tuple. The earlier engine copied the operand fact to the whole
// result register with no tuple accessor, so the downstream `extract #0`
// (which reads `result.tuple$0`) found nothing and taint was lost. The fix
// taints only the value slot `result.tuple$0` (leaving the `ok` bool clean)
// in BOTH flow directions: the forward gen in GoMethodSequentFlowFunction and
// the matching backward precondition in GoMethodSequentPrecondition. With the
// extract result correctly tainted, the pre-existing SSA-phi handling merges
// the `dir = v` (ok edge) and `dir = "safe"` (!ok edge) definitions, and the
// sink reads the tainted phi result.

func typeSwitchBinding001T() {
	var obj interface{} = util.Source()
	dir := "safe"
	switch v := obj.(type) {
	case string:
		dir = v
	}
	util.Sink(dir)
}

func typeSwitchBinding002F() {
	var obj interface{} = "safe"
	_ = util.Source()
	dir := "init"
	switch v := obj.(type) {
	case string:
		dir = v
	}
	util.Sink(dir)
}
