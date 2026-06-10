package test
import "test/util"


// ── Struct embedding tests ───────────────────────────────────────────

// ── Basic embedding ──────────────────────────────────────────────────

type EmbBase struct {
	baseValue string
}

func (b EmbBase) GetBaseValue() string { return b.baseValue }

type EmbDerived struct {
	EmbBase
	derivedValue string
}

func embeddedField001T() {
	data := util.Source()
	d := EmbDerived{
		EmbBase:      EmbBase{baseValue: data},
		derivedValue: "safe",
	}
	util.Sink(d.baseValue) // access promoted field
}

func embeddedField002F() {
	data := util.Source()
	d := EmbDerived{
		EmbBase:      EmbBase{baseValue: data},
		derivedValue: "safe",
	}
	util.Sink(d.derivedValue)
}

func embeddedMethod001T() {
	data := util.Source()
	d := EmbDerived{
		EmbBase:      EmbBase{baseValue: data},
		derivedValue: "safe",
	}
	result := d.GetBaseValue() // promoted method
	util.Sink(result)
}

func embeddedMethod002F() {
	_ = util.Source()
	d := EmbDerived{
		EmbBase:      EmbBase{baseValue: "safe"},
		derivedValue: "safe",
	}
	result := d.GetBaseValue()
	util.Sink(result)
}

// ── Multi-level embedding ────────────────────────────────────────────

type EmbLevel2 struct {
	EmbDerived
	level2Value string
}

func embeddedDeep001T() {
	data := util.Source()
	obj := EmbLevel2{
		EmbDerived: EmbDerived{
			EmbBase:      EmbBase{baseValue: data},
			derivedValue: "safe",
		},
		level2Value: "safe",
	}
	util.Sink(obj.baseValue) // promoted through two levels
}

func embeddedDeep002F() {
	data := util.Source()
	obj := EmbLevel2{
		EmbDerived: EmbDerived{
			EmbBase:      EmbBase{baseValue: data},
			derivedValue: "safe",
		},
		level2Value: "safe",
	}
	util.Sink(obj.level2Value)
}

// ── Interface embedding ──────────────────────────────────────────────

type EmbReader interface {
	Read() string
}

type EmbWriter interface {
	Write(data string)
}

type EmbReadWriter interface {
	EmbReader
	EmbWriter
}

type EmbRWImpl struct {
	data string
}

func (rw *EmbRWImpl) Read() string      { return rw.data }
func (rw *EmbRWImpl) Write(data string) { rw.data = data }

func embeddedInterface001T() {
	data := util.Source()
	var rw EmbReadWriter = &EmbRWImpl{data: data}
	result := rw.Read()
	util.Sink(result)
}

func embeddedInterface002F() {
	_ = util.Source()
	var rw EmbReadWriter = &EmbRWImpl{data: "safe"}
	result := rw.Read()
	util.Sink(result)
}
