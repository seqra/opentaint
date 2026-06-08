package test
import "test/util"


// ── Edge case tests ──────────────────────────────────────────────────

// ── Nil/zero value handling ──────────────────────────────────────────

func nilSlice001F() {
	_ = util.Source()
	var s []string
	if s != nil {
		util.Sink(s[0])
	}
}

func nilMap001F() {
	_ = util.Source()
	var m map[string]string
	if m != nil {
		util.Sink(m["k"])
	}
}

// ── Empty struct ─────────────────────────────────────────────────────

type EdgeEmpty struct{}

func emptyStruct001F() {
	_ = util.Source()
	e := EdgeEmpty{}
	_ = e
	util.Sink("safe")
}

// ── Very long assignment chain ───────────────────────────────────────

func longChain001T() {
	v0 := util.Source()
	v1 := v0
	v2 := v1
	v3 := v2
	v4 := v3
	v5 := v4
	v6 := v5
	v7 := v6
	v8 := v7
	v9 := v8
	util.Sink(v9)
}

func longChain002F() {
	v0 := util.Source()
	_ = v0
	v1 := "safe"
	v2 := v1
	v3 := v2
	v4 := v3
	v5 := v4
	v6 := v5
	v7 := v6
	v8 := v7
	v9 := v8
	util.Sink(v9)
}

// ── Taint through multiple function hops ─────────────────────────────

func hop1(x string) string { return hop2(x) }
func hop2(x string) string { return hop3(x) }
func hop3(x string) string { return hop4(x) }
func hop4(x string) string { return hop5(x) }
func hop5(x string) string { return x }

func deepHop001T() {
	data := util.Source()
	result := hop1(data)
	util.Sink(result)
}

func deepHop002F() {
	_ = util.Source()
	result := hop1("safe")
	util.Sink(result)
}

// ── Recursive function ───────────────────────────────────────────────

func recurse(s string, n int) string {
	if n <= 0 {
		return s
	}
	return recurse(s, n-1)
}

func recursive001T() {
	data := util.Source()
	result := recurse(data, 3)
	util.Sink(result)
}

func recursive002F() {
	_ = util.Source()
	result := recurse("safe", 3)
	util.Sink(result)
}

// ── Same variable reused in different contexts ───────────────────────

func reuseVar001T() {
	x := util.Source()
	util.Sink(x) // first use — tainted
}

func reuseVar002F() {
	x := util.Source()
	x = "safe"
	util.Sink(x) // second use — overwritten
}

func reuseVar003T() {
	x := "safe"
	x = util.Source()
	util.Sink(x) // overwritten with taint
}

// ── Taint through temp variable ──────────────────────────────────────

func tempVar001T() {
	data := util.Source()
	tmp := data
	data = "safe"
	util.Sink(tmp) // tmp still holds tainted value
}

func tempVar002F() {
	data := util.Source()
	tmp := "safe"
	_ = data
	util.Sink(tmp)
}

// ── Multiple returns from same function ──────────────────────────────

func edgeMultiCall001T() {
	data := util.Source()
	r1 := identity(data)
	r2 := identity("safe")
	util.Sink(r1)
	util.Consume(r2)
}

func edgeMultiCall002F() {
	data := util.Source()
	r1 := identity("safe")
	r2 := identity(data)
	util.Sink(r1)
	util.Consume(r2)
}

// ── Struct literal with mixed taint ──────────────────────────────────

type EdgeMixed struct {
	a string
	b string
	c string
}

func structMixed001T() {
	data := util.Source()
	m := EdgeMixed{a: data, b: "safe", c: "safe"}
	util.Sink(m.a)
}

func structMixed002F() {
	data := util.Source()
	m := EdgeMixed{a: data, b: "safe", c: "safe"}
	util.Sink(m.b)
}

func structMixed003F() {
	data := util.Source()
	m := EdgeMixed{a: data, b: "safe", c: "safe"}
	util.Sink(m.c)
}

// ── Swap pattern ─────────────────────────────────────────────────────

func swapVars001T() {
	a := util.Source()
	b := "safe"
	tmp := a
	a = b
	b = tmp
	util.Sink(b) // b now holds original tainted value
	util.Consume(a)
}

func swapVars002F() {
	a := util.Source()
	b := "safe"
	tmp := a
	a = b
	b = tmp
	util.Sink(a) // a now holds "safe"
	util.Consume(b)
}
