package test
import "test/util"


// ── Generics tests (Go 1.18+) ───────────────────────────────────────

// ── Generic identity function ────────────────────────────────────────

func GenIdentity[T any](x T) T { return x }

func genericFunc001T() {
	data := util.Source()
	result := GenIdentity(data)
	util.Sink(result)
}

func genericFunc002F() {
	_ = util.Source()
	result := GenIdentity("safe")
	util.Sink(result)
}

func genericFuncInt001T() {
	data := util.SourceInt()
	result := GenIdentity(data)
	util.SinkInt(result)
}

// ── Generic container ────────────────────────────────────────────────

type GenBox[T any] struct {
	value T
}

func (b GenBox[T]) Get() T   { return b.value }
func (b *GenBox[T]) Set(v T) { b.value = v }

func genericBox001T() {
	data := util.Source()
	b := GenBox[string]{value: data}
	result := b.Get()
	util.Sink(result)
}

func genericBox002F() {
	_ = util.Source()
	b := GenBox[string]{value: "safe"}
	result := b.Get()
	util.Sink(result)
}

func genericBoxSet001T() {
	data := util.Source()
	b := &GenBox[string]{}
	b.Set(data)
	result := b.Get()
	util.Sink(result)
}

// ── Generic pair ─────────────────────────────────────────────────────

type GenPair[A any, B any] struct {
	first  A
	second B
}

func (p GenPair[A, B]) GetFirst() A  { return p.first }
func (p GenPair[A, B]) GetSecond() B { return p.second }

func genericPair001T() {
	data := util.Source()
	p := GenPair[string, string]{first: data, second: "safe"}
	result := p.GetFirst()
	util.Sink(result)
}

func genericPair002F() {
	data := util.Source()
	p := GenPair[string, string]{first: data, second: "safe"}
	result := p.GetSecond()
	util.Sink(result)
}
