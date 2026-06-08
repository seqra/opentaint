package test
import "test/util"


// ── Advanced interprocedural tests ───────────────────────────────────

// ── Mutual recursion ─────────────────────────────────────────────────

func mutualA(s string, n int) string {
	if n <= 0 {
		return s
	}
	return mutualB(s, n-1)
}

func mutualB(s string, n int) string {
	return mutualA(s, n-1)
}

func mutualRecursion001T() {
	data := util.Source()
	result := mutualA(data, 4)
	util.Sink(result)
}

func mutualRecursion002F() {
	_ = util.Source()
	result := mutualA("safe", 4)
	util.Sink(result)
}

// ── Function returning function result ───────────────────────────────

func wrapIdentity(s string) string {
	return identity(s)
}

func wrapDrop(s string) string {
	return dropValue(s)
}

func funcReturnFunc001T() {
	data := util.Source()
	result := wrapIdentity(data)
	util.Sink(result)
}

func funcReturnFunc002F() {
	data := util.Source()
	result := wrapDrop(data)
	util.Sink(result)
}

// ── Multiple callers of same function ────────────────────────────────

func multiCaller001T() {
	data := util.Source()
	r1 := identity(data)
	r2 := identity("safe")
	util.Sink(r1)
	util.Consume(r2)
}

func multiCaller002F() {
	data := util.Source()
	r1 := identity("safe")
	r2 := identity(data)
	util.Sink(r1)
	util.Consume(r2)
}

// ── Pass through multiple functions ──────────────────────────────────

func passA(s string) string { return passB(s) }
func passB(s string) string { return passC(s) }
func passC(s string) string { return s }

func multiPass001T() {
	data := util.Source()
	result := passA(data)
	util.Sink(result)
}

func multiPass002F() {
	_ = util.Source()
	result := passA("safe")
	util.Sink(result)
}

// ── Function with side effects on argument ───────────────────────────

type AdvHolder struct {
	data string
}

func fillHolder(h *AdvHolder, val string) {
	h.data = val
}

func advSideEffect001T() {
	data := util.Source()
	h := &AdvHolder{}
	fillHolder(h, data)
	util.Sink(h.data)
}

func advSideEffect002F() {
	_ = util.Source()
	h := &AdvHolder{}
	fillHolder(h, "safe")
	util.Sink(h.data)
}

// ── Builder pattern ──────────────────────────────────────────────────

type AdvBuilder struct {
	result string
}

func (b *AdvBuilder) Add(s string) *AdvBuilder {
	b.result = b.result + s
	return b
}

func (b *AdvBuilder) Build() string {
	return b.result
}

func builder001T() {
	data := util.Source()
	b := &AdvBuilder{}
	result := b.Add(data).Build()
	util.Sink(result)
}

func builder002F() {
	_ = util.Source()
	b := &AdvBuilder{}
	result := b.Add("safe").Build()
	util.Sink(result)
}

// ── Function that returns different values based on condition ─────────

func condReturn(s string, useIt bool) string {
	if useIt {
		return s
	}
	return "safe"
}

func condReturn001T() {
	data := util.Source()
	result := condReturn(data, true)
	util.Sink(result)
}

func condReturn002T() {
	// Conservative: analysis doesn't know runtime value of condition
	data := util.Source()
	result := condReturn(data, false)
	util.Sink(result)
}
