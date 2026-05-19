package test
import "test/util"


// ── Expression tests (binary ops, string concat, unary ops) ──────────

// ── String concatenation ─────────────────────────────────────────────

func stringConcat001T() {
	data := util.Source()
	result := "prefix_" + data
	util.Sink(result)
}

func stringConcat002T() {
	data := util.Source()
	result := data + "_suffix"
	util.Sink(result)
}

func stringConcat003T() {
	data := util.Source()
	result := "prefix_" + data + "_suffix"
	util.Sink(result)
}

func stringConcat004F() {
	_ = util.Source()
	result := "prefix_" + "safe" + "_suffix"
	util.Sink(result)
}

// ── String concatenation with += ─────────────────────────────────────

func stringConcatAssign001T() {
	data := util.Source()
	result := "prefix_"
	result += data
	util.Sink(result)
}

func stringConcatAssign002F() {
	_ = util.Source()
	result := "prefix_"
	result += "safe"
	util.Sink(result)
}

// ── Multiple concatenation chain ─────────────────────────────────────

func stringConcatChain001T() {
	data := util.Source()
	a := "a" + data
	b := a + "b"
	c := b + "c"
	util.Sink(c)
}

func stringConcatChain002F() {
	_ = util.Source()
	a := "a" + "safe"
	b := a + "b"
	c := b + "c"
	util.Sink(c)
}

// ── Integer arithmetic (kills taint) ─────────────────────────────────

func intArith001F() {
	data := util.SourceInt()
	result := data + 1
	util.SinkInt(result)
}

func intArith002F() {
	data := util.SourceInt()
	result := data * 2
	util.SinkInt(result)
}

// ── Boolean negation (kills taint) ───────────────────────────────────

func boolNeg001F() {
	data := util.SourceBool()
	result := !data
	util.SinkBool(result)
}

// ── Comparison (kills taint) ─────────────────────────────────────────

func comparison001F() {
	data := util.Source()
	result := data == "test"
	util.SinkBool(result)
}
