package test

import "test/util"

// ── Closures of two methods with the same name ───────────────────────
//
// twinT and twinF have the same methods. The closures of a twinT method and
// of the twinF method with the same name share the short name (`method$1`)
// and the signature. Every twinT method is vulnerable, every twinF method is
// safe.

type twinT struct{}

type twinF struct{}

type twinHolder struct {
	value string
}

// A call of a function value.

func (t *twinT) funcValue() {
	data := util.Source()
	type operation = func(a, b string) string
	concat := func(a, b string) string {
		return a + b
	}
	var op operation = concat
	data = op(data, "suffix")
	util.Sink(data)
}

func (t *twinF) funcValue() {
	data := util.Source()
	type operation = func(a, b string) string
	concat := func(a, b string) string {
		return b
	}
	var op operation = concat
	data = op(data, "suffix")
	util.Sink(data)
}

// A closure that returns a captured value.

func (t *twinT) capturedValue() {
	data := util.Source()
	captured := data
	lazyValue := func() string { return captured }
	data = lazyValue()
	util.Sink(data)
}

func (t *twinF) capturedValue() {
	data := util.Source()
	captured := data
	lazyValue := func() string {
		_ = captured
		return "safe"
	}
	data = lazyValue()
	util.Sink(data)
}

// A closure that returns a closure.

func (t *twinT) nestedClosure() {
	data := util.Source()
	stringReturner := func() func() string {
		return func() string {
			return data
		}
	}
	stringRet := stringReturner()
	data = stringRet()
	util.Sink(data)
}

func (t *twinF) nestedClosure() {
	data := util.Source()
	stringReturner := func() func() string {
		return func() string {
			_ = data
			return "safe"
		}
	}
	stringRet := stringReturner()
	data = stringRet()
	util.Sink(data)
}

// A closure that writes a captured value to a field through its parameter.

func (t *twinT) fieldWrite() {
	data := util.Source()
	captured := data
	holder := &twinHolder{}
	write := func(h *twinHolder) {
		h.value = captured
	}
	write(holder)
	data = holder.value
	util.Sink(data)
}

func (t *twinF) fieldWrite() {
	data := util.Source()
	captured := data
	holder := &twinHolder{}
	write := func(h *twinHolder) {
		_ = captured
		h.value = "safe"
	}
	write(holder)
	data = holder.value
	util.Sink(data)
}

// A closure that returns a key of a captured map.

func (t *twinT) mapKey() {
	data := util.Source()
	set := make(map[string]struct{})
	set[data] = struct{}{}
	data = func() string {
		for k := range set {
			return k
		}
		return "safe"
	}()
	util.Sink(data)
}

func (t *twinF) mapKey() {
	data := util.Source()
	set := make(map[string]struct{})
	set[data] = struct{}{}
	data = func() string {
		for range set {
			return "found"
		}
		return "safe"
	}()
	util.Sink(data)
}

// ── Entry points ─────────────────────────────────────────────────────

func closureTwinFuncValue001T() { (&twinT{}).funcValue() }
func closureTwinFuncValue002F() { (&twinF{}).funcValue() }

func closureTwinCapturedValue001T() { (&twinT{}).capturedValue() }
func closureTwinCapturedValue002F() { (&twinF{}).capturedValue() }

func closureTwinNestedClosure001T() { (&twinT{}).nestedClosure() }
func closureTwinNestedClosure002F() { (&twinF{}).nestedClosure() }

func closureTwinFieldWrite001T() { (&twinT{}).fieldWrite() }
func closureTwinFieldWrite002F() { (&twinF{}).fieldWrite() }

func closureTwinMapKey001T() { (&twinT{}).mapKey() }
func closureTwinMapKey002F() { (&twinF{}).mapKey() }
