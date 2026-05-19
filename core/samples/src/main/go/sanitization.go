package test
import "test/util"


// ── Sanitization and taint killing tests ─────────────────────────────

// ── Basic overwrite sanitization ─────────────────────────────────────

func sanitize001F() {
	data := util.Source()
	data = "safe"
	util.Sink(data)
}

func sanitize002T() {
	data := util.Source()
	other := data
	data = "safe" // kills data but not other
	util.Sink(other)
}

// ── Sanitization through function call ───────────────────────────────

func sanitize003F() {
	data := util.Source()
	result := dropValue(data)
	util.Sink(result)
}

func sanitize004T() {
	data := util.Source()
	_ = dropValue(data) // doesn't affect original
	util.Sink(data)
}

// ── Conditional sanitization ─────────────────────────────────────────

func sanitizeCond001T() {
	data := util.Source()
	if len(data) > 100 {
		data = "safe" // only sanitizes in one branch
	}
	util.Sink(data) // taint may still reach here (conservative)
}

func sanitizeCond002F() {
	data := util.Source()
	if true {
		data = "safe"
	} else {
		data = "also safe"
	}
	util.Sink(data)
}

// ── Sanitization in loop ─────────────────────────────────────────────

func sanitizeLoop001T() {
	data := util.Source()
	for i := 0; i < 3; i++ {
		if i == 2 {
			data = "safe"
		}
	}
	util.Sink(data) // conservative: taint may not have been killed
}

func sanitizeLoop002F() {
	data := util.Source()
	data = "safe"
	for i := 0; i < 3; i++ {
		// data stays safe
	}
	util.Sink(data)
}

// ── Multiple taint util.Sources, partial sanitization ─────────────────────

func sanitizePartial001T() {
	a := util.Source()
	b := util.Source()
	a = "safe" // kills a
	util.Sink(b)    // b still tainted
	util.Consume(a)
}

func sanitizePartial002F() {
	a := util.Source()
	b := util.Source()
	a = "safe"
	b = "safe"  // both killed
	util.Sink(a + b) // both safe now
}

// ── Struct field overwrite ───────────────────────────────────────────

func sanitizeField001T() {
	data := util.Source()
	p := SFPair{tainted: data, clean: "safe"}
	p.clean = "new safe" // doesn't affect tainted field
	util.Sink(p.tainted)
}

func sanitizeField002F() {
	data := util.Source()
	p := SFPair{tainted: data, clean: "safe"}
	p.tainted = "safe" // overwrites tainted field
	util.Sink(p.tainted)
}
