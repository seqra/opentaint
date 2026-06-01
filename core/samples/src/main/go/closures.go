package test
import "test/util"


// ── Closure and anonymous function tests ─────────────────────────────

// ── Basic anonymous functions ────────────────────────────────────────

func anonFunc001T() {
	data := util.Source()
	f := func(x string) string { return x }
	result := f(data)
	util.Sink(result)
}

func anonFunc002F() {
	data := util.Source()
	_ = data
	f := func(x string) string { return "safe" }
	result := f("anything")
	util.Sink(result)
}

func anonFuncDirect001T() {
	data := util.Source()
	result := func(x string) string { return x }(data)
	util.Sink(result)
}

func anonFuncDirect002F() {
	_ = util.Source()
	result := func(x string) string { return "safe" }("anything")
	util.Sink(result)
}

// ── Closures that capture variables ──────────────────────────────────

func closure001T() {
	data := util.Source()
	f := func() string { return data }
	result := f()
	util.Sink(result)
}

func closure002F() {
	data := util.Source()
	data = "safe"
	f := func() string { return data }
	result := f()
	util.Sink(result)
}

func closureModify001T() {
	data := "safe"
	f := func() {
		data = util.Source()
	}
	f()
	util.Sink(data)
}

func closureModify002F() {
	data := util.Source()
	f := func() {
		data = "safe"
	}
	f()
	util.Sink(data)
}

// ── Closure returned from function ───────────────────────────────────

func makeAdder(prefix string) func(string) string {
	return func(s string) string { return prefix + s }
}

func closureReturn001T() {
	data := util.Source()
	adder := makeAdder(data)
	result := adder("suffix")
	util.Sink(result)
}

func closureReturn002F() {
	_ = util.Source()
	adder := makeAdder("safe")
	result := adder("suffix")
	util.Sink(result)
}

// ── Higher-order functions ───────────────────────────────────────────

func applyFunc(f func(string) string, data string) string {
	return f(data)
}

func higherOrder001T() {
	data := util.Source()
	result := applyFunc(func(s string) string { return s }, data)
	util.Sink(result)
}

func higherOrder002F() {
	data := util.Source()
	_ = data
	result := applyFunc(func(s string) string { return "safe" }, "anything")
	util.Sink(result)
}

func higherOrder003T() {
	data := util.Source()
	result := applyFunc(identity, data)
	util.Sink(result)
}

func higherOrder004F() {
	data := util.Source()
	result := applyFunc(dropValue, data)
	util.Sink(result)
}

// ── Cluster C: factory returns a closure capturing tainted free var ──

func makeCapturingPrefixer(prefix string) func(string) string {
	return func(value string) string { return prefix + value }
}

func closureCaptureReturn001T() {
	data := util.Source()
	addPrefix := makeCapturingPrefixer(data)
	out := addPrefix("_suffix")
	util.Sink(out)
}

func closureCaptureReturn002F() {
	_ = util.Source()
	addPrefix := makeCapturingPrefixer("safe")
	out := addPrefix("_suffix")
	util.Sink(out)
}
