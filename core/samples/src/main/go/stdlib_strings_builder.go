package test

import (
	"strings"
	"test/util"
)

// ── Pattern 1: strings.Builder — WriteString + String round-trip ─────
//
// Empirical engine status: PASS (resolved 2026-05-28, Pattern 1).
//
// FULL per-instruction facts from `printFactsAt`:
//   L24 [0:0]  Source()                            facts: ∅
//   L25 [0:1]  new strings.Builder  // b           facts: var(0)![taint].$
//   L26 [0:2]  (*strings.Builder).WriteString(b,data) facts: ∅
//   L27 [0:3]  (*strings.Builder).String(b)        facts: var(0)![taint].$, var(1)![taint].$
//   L28 [0:4]  util.Sink(out)                      facts: var(1)![taint].$, var(3)![taint].$
//
// With strings.Builder passthrough rules now bundled, WriteString copies its
// arg into the Builder receiver and String() returns the receiver's taint, so
// var(1) (out) becomes tainted and reaches the sink. var(3) is the sink-arg fact.

func stringsBuilderWrite001T() {
	data := util.Source()
	b := strings.Builder{}
	b.WriteString(data)
	out := b.String()
	util.Sink(out)
}

func stringsBuilderWrite002F() {
	_ = util.Source()
	b := strings.Builder{}
	b.WriteString("safe")
	out := b.String()
	util.Sink(out)
}
