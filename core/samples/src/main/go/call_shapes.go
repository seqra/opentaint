package test

import "test/util"

// File focus: call resolution + argument propagation across the 11 IR call
// shapes enumerated in go-sast-current-design.md §4. Each function is the
// minimum that exercises one call shape; downstream taint propagation is
// kept trivial so a failure points at the call edge, not at field/closure
// state semantics.
//
// Type names get a CS prefix to avoid clashing with other fixtures in
// `package test`.

// ── Helpers ──────────────────────────────────────────────────────────

// Plain non-method function used by several shapes.
func csPass(x string) string { return x }

// Value-receiver struct.
type CSValRecv struct{}

func (c CSValRecv) Pass(x string) string { return x }

// Pointer-receiver struct.
type CSPtrRecv struct{}

func (c *CSPtrRecv) Pass(x string) string { return x }

// Interface satisfied structurally by CSValRecv (and CSPtrRecv).
type CSPasser interface {
	Pass(x string) string
}

// Inner type whose method is promoted into CSOuter.
type CSInner struct{}

func (i CSInner) Pass(x string) string { return x }

type CSOuter struct {
	CSInner
}

// Generic identity used by the generic-monomorphised case.
func CSIdentity[T any](x T) T { return x }

// ── 1. DIRECT non-method (plain function call) ───────────────────────

func directNonMethod001T() {
	d := util.Source()
	util.Sink(csPass(d))
}

func directNonMethod002F() {
	_ = util.Source()
	util.Sink(csPass("safe"))
}

// ── 2. DIRECT value-method (obj.M(x), value receiver) ────────────────

func directValueMethod001T() {
	d := util.Source()
	c := CSValRecv{}
	util.Sink(c.Pass(d))
}

func directValueMethod002F() {
	_ = util.Source()
	c := CSValRecv{}
	util.Sink(c.Pass("safe"))
}

// ── 3. DIRECT pointer-method (obj.M(x), pointer receiver) ────────────

func directPointerMethod001T() {
	d := util.Source()
	c := &CSPtrRecv{}
	util.Sink(c.Pass(d))
}

func directPointerMethod002F() {
	_ = util.Source()
	c := &CSPtrRecv{}
	util.Sink(c.Pass("safe"))
}

// ── 4. INVOKE (interface method dispatch) ────────────────────────────

func invoke001T() {
	d := util.Source()
	var p CSPasser = CSValRecv{}
	util.Sink(p.Pass(d))
}

func invoke002F() {
	_ = util.Source()
	var p CSPasser = CSValRecv{}
	util.Sink(p.Pass("safe"))
}

// ── 5. DYNAMIC plain (function-valued variable) ──────────────────────

func dynamicPlain001T() {
	d := util.Source()
	f := csPass
	util.Sink(f(d))
}

func dynamicPlain002F() {
	_ = util.Source()
	f := csPass
	util.Sink(f("safe"))
}

// ── 6. DYNAMIC bound-method (m := obj.M; m(x)) ───────────────────────

func dynamicBoundMethod001T() {
	d := util.Source()
	c := CSValRecv{}
	m := c.Pass
	util.Sink(m(d))
}

func dynamicBoundMethod002F() {
	_ = util.Source()
	c := CSValRecv{}
	m := c.Pass
	util.Sink(m("safe"))
}

// ── 7. Method expression (T.M; m(obj, x)) ────────────────────────────

func methodExpression001T() {
	d := util.Source()
	me := CSValRecv.Pass
	util.Sink(me(CSValRecv{}, d))
}

func methodExpression002F() {
	_ = util.Source()
	me := CSValRecv.Pass
	util.Sink(me(CSValRecv{}, "safe"))
}

// ── 8. Embedded promoted method ──────────────────────────────────────

func embeddedPromoted001T() {
	d := util.Source()
	o := CSOuter{}
	util.Sink(o.Pass(d))
}

func embeddedPromoted002F() {
	_ = util.Source()
	o := CSOuter{}
	util.Sink(o.Pass("safe"))
}

// ── 9. Builtin (append, propagating element taint) ───────────────────

func builtin001T() {
	d := util.Source()
	s := append([]string{}, d)
	util.Sink(s[0])
}

func builtin002F() {
	_ = util.Source()
	s := append([]string{}, "safe")
	util.Sink(s[0])
}

// ── 10. Unresolved DYNAMIC (function from map lookup) ────────────────
//
// The function value `f` comes from a map lookup; the call resolver
// cannot statically trace `f` to a MakeClosure, so the call is
// unresolved-DYNAMIC. The engine should treat the call as opaque,
// firing only pass-through rules (none configured here).

func unresolvedDynamic001T() {
	d := util.Source()
	m := map[string]func(string) string{"k": csPass}
	f := m["k"]
	util.Sink(f(d))
}

func unresolvedDynamic002F() {
	_ = util.Source()
	m := map[string]func(string) string{"k": csPass}
	f := m["k"]
	util.Sink(f("safe"))
}

// ── 11. Generic monomorphised ────────────────────────────────────────

func genericMonomorphised001T() {
	d := util.Source()
	util.Sink(CSIdentity[string](d))
}

func genericMonomorphised002F() {
	_ = util.Source()
	util.Sink(CSIdentity[string]("safe"))
}
