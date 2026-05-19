package test
import "test/util"


// ── Closure capture and invocation pattern tests ─────────────────────

// ── Direct capture of tainted variable ───────────────────────────────

func closureCapture001T() {
	data := util.Source()
	f := func() string { return data }
	util.Sink(f())
}

func closureCapture002F() {
	data := util.Source()
	data = "safe"
	f := func() string { return data }
	util.Sink(f())
}

// ── Closure capturing two variables ──────────────────────────────────

func closureTwoVars001T() {
	tainted := util.Source()
	clean := "safe"
	f := func() string { return tainted + clean }
	util.Sink(f())
}

func closureTwoVars002F() {
	tainted := util.Source()
	clean := "safe"
	util.Consume(tainted)
	f := func() string { return clean }
	util.Sink(f())
}

// ── Nested closures ──────────────────────────────────────────────────

func closureNested001T() {
	data := util.Source()
	outer := func() func() string {
		return func() string { return data }
	}
	inner := outer()
	util.Sink(inner())
}

func closureNested002F() {
	data := util.Source()
	util.Consume(data)
	safe := "clean"
	outer := func() func() string {
		return func() string { return safe }
	}
	inner := outer()
	util.Sink(inner())
}

// ── Closure assigned to variable then called ─────────────────────────

func closureAssign001T() {
	data := util.Source()
	var f func() string
	f = func() string { return data }
	result := f()
	util.Sink(result)
}

func closureAssign002F() {
	_ = util.Source()
	var f func() string
	f = func() string { return "constant" }
	result := f()
	util.Sink(result)
}

// ── Closure capturing slice ──────────────────────────────────────────

func closureSlice001T() {
	data := util.Source()
	items := []string{data, "b", "c"}
	f := func() string { return items[0] }
	util.Sink(f())
}

func closureSlice002F() {
	_ = util.Source()
	items := []string{"safe", "b", "c"}
	f := func() string { return items[0] }
	util.Sink(f())
}
