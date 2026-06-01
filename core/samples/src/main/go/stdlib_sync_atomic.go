package test

import (
	"sync/atomic"
	"test/util"
)

// ── Pattern 3: sync/atomic.Value — Store + Load + type-assert ────────
//
// Empirical engine status (with bundled go-config): PASS.
// assertReachable("test.atomicValueLoad001T") succeeds.
//
// Per-instruction facts from `printFactsAt`:
//   L12 [0:1]  new sync/atomic.Value                    facts: var(0)![taint].$
//   L13 [0:3]  (*sync/atomic.Value).Store(v, data)      facts: var(2)![taint].$
//   L14 [0:4]  (*sync/atomic.Value).Load(v)             facts: var(1)![taint].$, var(2)![taint].$
//   L14 [0:5]  result.(string)                          facts: var(1)![taint].$, var(4)![taint].$
//   L15 [0:6]  util.Sink(s)                             facts: var(5)![taint].$
//   L-1 [0:7]  return                                   facts: var(5)![taint].$
//
// Store/Load receiver-method rules in sync.atomic.yaml (from: arg(0) to: this)
// + (from: this to: result), loaded via GoConfigLoader, plus the existing
// type-assertion handling, carry taint all the way to Sink. No engine change
// needed for this pattern.

func atomicValueLoad001T() {
	data := util.Source()
	var v atomic.Value
	v.Store(data)
	s := v.Load().(string)
	util.Sink(s)
}

func atomicValueLoad002F() {
	_ = util.Source()
	var v atomic.Value
	v.Store("safe")
	s := v.Load().(string)
	util.Sink(s)
}
