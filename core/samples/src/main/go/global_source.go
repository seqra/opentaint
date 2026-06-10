package test

import (
	"os"
	"test/util"
)

// Tests for GlobalReadSource rules through trace resolution.
// Rule under test in GlobalSourceTraceTest.kt configures os.Args as
// a GlobalReadSource — the engine fires applyGlobalReadSourceRules on
// the os.Args[i] SSA chain, the test asserts that the produced
// vulnerability resolves a trace successfully.

func globalSource001T() {
	arg := os.Args[1]
	util.Sink(arg)
}

func globalSource002F() {
	_ = os.Args[1]
	util.Sink("safe")
}
