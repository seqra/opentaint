package test
import "test/util"


// ── Multi-return pattern tests ───────────────────────────────────────

// ── Swap returns ─────────────────────────────────────────────────────

func swapReturns(a string, b string) (string, string) {
	return b, a
}

func multiRetSwap001T() {
	data := util.Source()
	first, _ := swapReturns("clean", data)
	util.Sink(first)
}

func multiRetSwap002F() {
	data := util.Source()
	_, second := swapReturns("clean", data)
	util.Sink(second)
}

// ── Chain of multi-return calls ──────────────────────────────────────

func pairPass(a string, b string) (string, string) {
	return a, b
}

func multiRetChain001T() {
	data := util.Source()
	x, _ := pairPass(data, "clean")
	result, _ := pairPass(x, "other")
	util.Sink(result)
}

func multiRetChain002F() {
	data := util.Source()
	_, y := pairPass(data, "clean")
	_, result := pairPass("other", y)
	util.Sink(result)
}

// ── Multi-return used inside another function call ───────────────────

func firstOf(a string, b string) string {
	return a
}

func multiRetFunc001T() {
	data := util.Source()
	a, _ := pairPass(data, "clean")
	result := firstOf(a, "safe")
	util.Sink(result)
}

func multiRetFunc002F() {
	data := util.Source()
	_, b := pairPass(data, "clean")
	result := firstOf("safe", b)
	util.Sink(result)
}

// ── Discarding returns with _ ────────────────────────────────────────

func multiRetIgnore001T() {
	data := util.Source()
	result, _ := pairPass(data, "clean")
	util.Sink(result)
}

func multiRetIgnore002F() {
	data := util.Source()
	_, _ = pairPass(data, "clean")
	util.Sink("safe")
}
