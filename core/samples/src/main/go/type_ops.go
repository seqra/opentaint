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
