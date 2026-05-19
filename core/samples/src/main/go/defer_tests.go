package test
import "test/util"


// ── Defer execution order tests ──────────────────────────────────────
// Defer args are evaluated immediately, but the call runs after surrounding code.

// ── Basic defer ──────────────────────────────────────────────────────

func defer001T() {
	data := util.Source()
	defer util.Consume(data) // deferred, but data is tainted at eval time
	util.Sink(data)          // util.Sink runs before defer body
}

func defer002F() {
	data := "safe"
	defer util.Consume(data)
	util.Sink(data) // data is safe here
}

// ── Defer with util.Sink ──────────────────────────────────────────────────

func deferSink001T() {
	data := util.Source()
	defer util.Sink(data) // args evaluated immediately: data is tainted
}

func deferSink002F() {
	data := "safe"
	defer util.Sink(data) // args evaluated immediately: data is safe
	data = util.Source()  // this happens after defer eval, before defer runs
	util.Consume(data)
}

// ── Defer in loop ────────────────────────────────────────────────────

func deferLoop001T() {
	data := util.Source()
	for i := 0; i < 1; i++ {
		defer util.Sink(data)
	}
}

// ── Defer with closure ───────────────────────────────────────────────

func deferClosure001T() {
	data := util.Source()
	defer func() {
		util.Sink(data) // closure captures data; data is tainted at call time
	}()
}

func deferClosure002F() {
	data := util.Source()
	data = "safe"
	defer func() {
		util.Sink(data) // data was overwritten before defer was set up
	}()
}

// ── Multiple defers (LIFO order) ─────────────────────────────────────

func deferMultiple001T() {
	data := util.Source()
	defer util.Consume(data)
	defer util.Sink(data) // this runs before the consume defer
}
