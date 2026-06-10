package test
import "test/util"


// ── Combination / stress tests ───────────────────────────────────────
// Tests that combine multiple features to verify complex interactions.

// ── Struct + interface + method call chain ────────────────────────────

type CombProcessor interface {
	Process() string
}

type CombTainted struct {
	data string
}

func (c CombTainted) Process() string { return c.data }

type CombSafe struct{}

func (c CombSafe) Process() string { return "safe" }

func combStructInterface001T() {
	data := util.Source()
	var p CombProcessor = CombTainted{data: data}
	result := p.Process()
	util.Sink(result)
}

func combStructInterface002F() {
	_ = util.Source()
	var p CombProcessor = CombSafe{}
	result := p.Process()
	util.Sink(result)
}

// ── Closure + struct field ───────────────────────────────────────────

func combClosureField001T() {
	data := util.Source()
	p := SFPair{tainted: data, clean: "safe"}
	f := func() string { return p.tainted }
	result := f()
	util.Sink(result)
}

func combClosureField002F() {
	data := util.Source()
	p := SFPair{tainted: data, clean: "safe"}
	f := func() string { return p.clean }
	result := f()
	util.Sink(result)
}

// ── Map + function call + multi-return ───────────────────────────────

func combMapFunc001T() {
	data := util.Source()
	m := map[string]string{"key": data}
	result, _ := twoReturns(m["key"], "clean")
	util.Sink(result)
}

func combMapFunc002F() {
	data := util.Source()
	m := map[string]string{"key": data}
	_, result := twoReturns(m["key"], "clean")
	util.Sink(result)
}

// ── Slice + loop + function call ─────────────────────────────────────

func combSliceLoop001T() {
	data := util.Source()
	s := []string{"a", data, "b"}
	var result string
	for _, v := range s {
		result = identity(v)
	}
	util.Sink(result)
}

func combSliceLoop002F() {
	data := util.Source()
	s := []string{"a", data, "b"}
	var result string
	for _, v := range s {
		result = dropValue(v)
	}
	util.Sink(result)
}

// ── Pointer + method + interface ─────────────────────────────────────

func combPtrMethod001T() {
	data := util.Source()
	obj := &MRPtrContainer{}
	obj.SetValue(data)
	result := obj.GetValue()
	util.Sink(result)
}

func combPtrMethod002F() {
	_ = util.Source()
	obj := &MRPtrContainer{}
	obj.SetValue("safe")
	result := obj.GetValue()
	util.Sink(result)
}

// ── Nested function calls + struct ───────────────────────────────────

func wrapInPair(data string) SFPair {
	return SFPair{tainted: data, clean: "safe"}
}

func extractFromPair(p SFPair) string {
	return p.tainted
}

func combNestedFunc001T() {
	data := util.Source()
	result := extractFromPair(wrapInPair(data))
	util.Sink(result)
}

func combNestedFunc002F() {
	_ = util.Source()
	result := extractFromPair(wrapInPair("safe"))
	// wrapInPair puts "safe" in tainted field, so extractFromPair returns "safe"
	// However, the field is literally "safe" string, not tainted
	util.Sink(result)
}

// ── Deep chain: closure capturing struct returned from func ──────────

func combDeepChain001T() {
	data := util.Source()
	p := wrapInPair(data)
	f := func() string {
		return extractFromPair(p)
	}
	result := f()
	util.Sink(result)
}

func combDeepChain002F() {
	_ = util.Source()
	p := wrapInPair("safe")
	f := func() string {
		return extractFromPair(p)
	}
	result := f()
	util.Sink(result)
}

// ── Struct field + slice element ─────────────────────────────────────

type CombHolder struct {
	items []string
}

func combStructSlice001T() {
	data := util.Source()
	h := CombHolder{items: []string{data}}
	util.Sink(h.items[0])
}

func combStructSlice002F() {
	_ = util.Source()
	h := CombHolder{items: []string{"safe"}}
	util.Sink(h.items[0])
}

// ── Multiple assignments in sequence ─────────────────────────────────

func combSequence001T() {
	a := util.Source()
	b := a
	c := b
	d := c
	e := d
	util.Sink(e)
}

func combSequence002F() {
	a := util.Source()
	b := a
	_ = b
	c := "safe"
	d := c
	e := d
	util.Sink(e)
}
