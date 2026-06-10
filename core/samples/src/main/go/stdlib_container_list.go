package test

import (
	"container/list"
	"test/util"
)

// ── Pattern 2: container/list — PushBack + Front + Value type-assert ─
//
// Empirical engine status (with bundled go-config): PASS.
// assertReachable("test.containerListPushFront001T") succeeds.
//
// Full per-instruction facts from `printFactsAt` (after the loader fix):
//   L37 [0:1]  container/list.New()                      facts: var(0)![taint].$
//   L-1 [0:2]  makeinterface(data)                       facts: ∅
//   L38 [0:3]  (*container/list.List).PushBack(l, data)  facts: var(2)![taint].$
//   L39 [0:4]  (*container/list.List).Front(l)           facts: var(1)[*]![taint].$,
//                                                                var(2)![taint].$,
//                                                                var(3).Value![taint].$
//   L40 [0:5]  &e.Value                                  facts: var(1)[*]…, var(4).Value![taint].$
//   L40 [0:6]  *&e.Value                                 facts: var(5)![taint].$
//   L40 [0:7]  result.(string)                           facts: var(6)![taint].$
//   L41 [0:8]  util.Sink(v)                              facts: var(7)![taint].$
//
// Was a confirmed FN (root cause: the bundled container.list.yaml PushBack/
// Front rules use Go pseudo-accessor field modifiers
// `.container/list.List#<element>` and `.container/list.Element#Value` —
// each has only ONE `#`. The shared Field deserialiser regex in
// SerializedPosition.kt requires THREE `#`-separated parts
// (className#fieldName#fieldType), so the one-`#` form failed, the copy
// action dropped, and the whole rule was discarded → the list element was
// never modelled). Fixed in GoConfigLoader.parseGoPositionModifier:
// `.Type#<element>`/`.<map>#<value|key>` now map to the element accessor and
// `.Type#field` (e.g. Element#Value) maps to Field(Type, field, fieldType),
// where fieldType is the read-site type `*interface{...}` so the synthesised
// accessor matches the real `&e.Value` field-addr read. `<pointer>#<deref>`
// is treated as the identity accessor and dropped without failing the
// position.

func containerListPushFront001T() {
	data := util.Source()
	l := list.New()
	l.PushBack(data)
	e := l.Front()
	v := e.Value.(string)
	util.Sink(v)
}

func containerListPushFront002F() {
	_ = util.Source()
	l := list.New()
	l.PushBack("safe")
	e := l.Front()
	v := e.Value.(string)
	util.Sink(v)
}
