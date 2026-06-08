package test
import "test/util"


// ── Helper functions for interprocedural tests ──────────────────────

func identity(x string) string          { return x }
func identityChain(x string) string     { return identity(x) }
func identityChainDeep(x string) string { return identityChain(x) }
func selectFirst(a, b string) string    { return a }
func selectSecond(a, b string) string   { return b }
func dropValue(x string) string         { return "safe" }

// ── Argument/return passing ─────────────────────────────────────────

func returnValuePassing001F() {
	taintSrc := util.Source()
	result := dropValue(taintSrc)
	util.Sink(result)
}

func returnValuePassing002T() {
	taintSrc := util.Source()
	result := identity(taintSrc)
	util.Sink(result)
}

func argPassing001F() {
	taintSrc := util.Source()
	result := selectSecond(taintSrc, "clean")
	util.Sink(result)
}

func argPassing002T() {
	taintSrc := util.Source()
	result := selectFirst(taintSrc, "clean")
	util.Sink(result)
}

func argPassing005F() {
	taintSrc := util.Source()
	result := selectFirst("clean", taintSrc)
	util.Sink(result)
}

func argPassing006T() {
	taintSrc := util.Source()
	result := selectSecond("clean", taintSrc)
	util.Sink(result)
}

// ── Deep call chains ────────────────────────────────────────────────

func deepCall001T() {
	data := util.Source()
	result := identity(data)
	util.Sink(result)
}

func deepCall002T() {
	data := util.Source()
	result := identityChain(data)
	util.Sink(result)
}

func deepCall003T() {
	data := util.Source()
	result := identityChainDeep(data)
	util.Sink(result)
}

func deepCallClean001F() {
	data := util.Source()
	_ = data
	result := identity("safe")
	util.Sink(result)
}

// ── Argument position sensitivity ───────────────────────────────────

func argPosition001T() {
	data := util.Source()
	result := selectFirst(data, "clean")
	util.Sink(result)
}

func argPosition002F() {
	data := util.Source()
	result := selectSecond(data, "clean")
	util.Sink(result)
}
