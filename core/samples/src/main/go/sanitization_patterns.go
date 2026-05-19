package test
import "test/util"


// ── Sanitization pattern tests ───────────────────────────────────────

// ── Conditional sanitization ─────────────────────────────────────────

func sanitizeConditional001T() {
	data := util.Source()
	if len(data) > 5 {
		data = util.Sanitize(data)
	}
	// only one branch sanitizes → conservative: still tainted
	util.Sink(data)
}

func sanitizeConditional002F() {
	data := util.Source()
	if len(data) > 5 {
		data = "safe1"
	} else {
		data = "safe2"
	}
	util.Sink(data)
}

// ── Return from function (identity vs constant) ──────────────────────

func sanitizeReturn001T() {
	data := util.Source()
	result := identity(data)
	util.Sink(result)
}

func sanitizeReturn002F() {
	data := util.Source()
	result := dropValue(data)
	util.Sink(result)
}

// ── Chain of functions ───────────────────────────────────────────────

func sanitizeChain001T() {
	data := util.Source()
	step1 := identity(data)
	step2 := util.Passthrough(step1)
	util.Sink(step2)
}

func sanitizeChain002F() {
	data := util.Source()
	step1 := identity(data)
	step2 := dropValue(step1)
	util.Sink(step2)
}

// ── Reassignment of tainted variable ─────────────────────────────────

func sanitizeReassign001T() {
	data := util.Source()
	original := data
	data = "safe"
	// original still holds taint
	util.Sink(original)
}

func sanitizeReassign002F() {
	data := util.Source()
	data = "safe"
	util.Sink(data)
}
