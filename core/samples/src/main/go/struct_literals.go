package test

import "test/util"

type SLData struct {
	value string
	extra string
}

type SLOuter struct {
	inner SLData
	tag   string
}

func readSLValue(d SLData) string { return d.value }

func (d SLData) getValue() string { return d.value }

func fillSLData(p *SLData, v string) { *p = SLData{value: v, extra: "x"} }

// ── Literal assigned to a new variable ───────────────────────────────

func structLit001T() {
	d := SLData{value: util.Source(), extra: "x"}
	util.Sink(d.value)
}

func structLit002F() {
	d := SLData{value: util.Source(), extra: "x"}
	util.Sink(d.extra)
}

func structLitUnkeyed001T() {
	d := SLData{util.Source(), "x"}
	util.Sink(d.value)
}

func structLitUnkeyed002F() {
	d := SLData{util.Source(), "x"}
	util.Sink(d.extra)
}

func structLitPointer001T() {
	p := &SLData{value: util.Source(), extra: "x"}
	util.Sink(p.value)
}

func structLitPointer002F() {
	p := &SLData{value: util.Source(), extra: "x"}
	util.Sink(p.extra)
}

// ── Literal assigned over an existing value ──────────────────────────

func structLitReassign001T() {
	d := SLData{value: "safe"}
	d = SLData{value: util.Source()}
	util.Sink(d.value)
}

func structLitReassign002F() {
	d := SLData{value: util.Source()}
	d = SLData{value: "safe"}
	util.Sink(d.value)
}

func structLitReassign003F() {
	d := SLData{value: util.Source()}
	d = SLData{extra: "x"}
	util.Sink(d.value)
}

func structLitThroughPointer001T() {
	d := &SLData{}
	fillSLData(d, util.Source())
	util.Sink(d.value)
}

func structLitThroughPointer002F() {
	d := &SLData{}
	fillSLData(d, util.Source())
	util.Sink(d.extra)
}

func structLitThroughPointer003F() {
	p := &SLData{value: util.Source()}
	*p = SLData{value: "safe"}
	util.Sink(p.value)
}

func structLitAddressTaken001T() {
	d := SLData{value: "safe"}
	q := &d
	d = SLData{value: util.Source()}
	util.Sink(q.value)
}

func structLitAddressTaken002F() {
	d := SLData{value: util.Source()}
	q := &d
	d = SLData{value: "safe"}
	util.Sink(q.value)
}

func structLitInLoop001T() {
	var d SLData
	for i := 0; i < 3; i++ {
		d = SLData{value: util.Source()}
	}
	util.Sink(d.value)
}

func structLitInBranch001T(c bool) {
	d := SLData{value: "safe"}
	if c {
		d = SLData{value: util.Source()}
	}
	util.Sink(d.value)
}

// ── Literal stored into a field, an element or a nested literal ──────

func structLitToField001T() {
	o := SLOuter{}
	o.inner = SLData{value: util.Source()}
	util.Sink(o.inner.value)
}

func structLitToField002F() {
	o := SLOuter{}
	o.inner = SLData{value: util.Source()}
	util.Sink(o.tag)
}

func structLitNested001T() {
	o := SLOuter{inner: SLData{value: util.Source()}, tag: "t"}
	util.Sink(o.inner.value)
}

func structLitNested002F() {
	o := SLOuter{inner: SLData{value: util.Source()}, tag: "t"}
	util.Sink(o.inner.extra)
}

func structLitNested003F() {
	o := SLOuter{inner: SLData{value: util.Source()}, tag: "t"}
	util.Sink(o.tag)
}

func structLitInSlice001T() {
	s := []SLData{{value: util.Source()}}
	util.Sink(s[0].value)
}

func structLitInSlice002F() {
	s := []SLData{{value: util.Source()}}
	util.Sink(s[0].extra)
}

func structLitInArray001T() {
	arr := [2]SLData{{value: util.Source()}, {value: "x"}}
	util.Sink(arr[0].value)
}

func structLitInMap001T() {
	m := map[string]SLData{"k": {value: util.Source()}}
	util.Sink(m["k"].value)
}

func structLitPointerElements001T() {
	s := []*SLData{{value: util.Source()}}
	util.Sink(s[0].value)
}

// ── Literal used as a value ──────────────────────────────────────────

func structLitAsArgument001T() {
	util.Sink(readSLValue(SLData{value: util.Source()}))
}

func structLitAsArgument002F() {
	util.Sink(readSLValue(SLData{extra: util.Source()}))
}

func structLitAsReceiver001T() {
	util.Sink(SLData{value: util.Source()}.getValue())
}

func structLitInInterface001T() {
	var i interface{} = SLData{value: util.Source()}
	d := i.(SLData)
	util.Sink(d.value)
}

func structLitCaptured001T() {
	d := SLData{value: util.Source()}
	f := func() string { return d.value }
	util.Sink(f())
}

// ── Empty literals ───────────────────────────────────────────────────

func structLitEmpty001F() {
	d := SLData{value: util.Source()}
	d = SLData{}
	util.Sink(d.value)
}

func arrayLitEmpty001F() {
	a := [2]string{util.Source(), "x"}
	a = [2]string{}
	util.Sink(a[0])
}

func arrayLitEmpty002T() {
	a := [2]string{}
	a[0] = util.Source()
	util.Sink(a[0])
}
