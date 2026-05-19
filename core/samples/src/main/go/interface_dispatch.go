package test
import "test/util"


// ── Interface dispatch (INVOKE) tests ────────────────────────────────

// IDProcessor is an interface with a single method
type IDProcessor interface {
	Process(data string) string
}

// IDTaintedProcessor returns its input (preserves taint)
type IDTaintedProcessor struct{}

func (p IDTaintedProcessor) Process(data string) string { return data }

// IDCleanProcessor ignores its input and returns "safe"
type IDCleanProcessor struct{}

func (p IDCleanProcessor) Process(data string) string { return "safe" }

// IDReader interface for reading data
type IDReader interface {
	Read() string
}

// IDTaintedReader holds tainted data
type IDTaintedReader struct{ data string }

func (r IDTaintedReader) Read() string { return r.data }

// IDCleanReader always returns clean data
type IDCleanReader struct{}

func (r IDCleanReader) Read() string { return "clean" }

// ── Tests ────────────────────────────────────────────────────────────

func polymorphism001T() {
	data := util.Source()
	var p IDProcessor = IDTaintedProcessor{}
	result := p.Process(data)
	util.Sink(result)
}

func polymorphism002F() {
	data := util.Source()
	var p IDProcessor = IDCleanProcessor{}
	result := p.Process(data)
	util.Sink(result)
}

func interfaceClass001T() {
	data := util.Source()
	var r IDReader = IDTaintedReader{data: data}
	result := r.Read()
	util.Sink(result)
}

func interfaceClass002F() {
	_ = util.Source()
	var r IDReader = IDCleanReader{}
	result := r.Read()
	util.Sink(result)
}

func interfaceViaFunc001T() {
	data := util.Source()
	var p IDProcessor = IDTaintedProcessor{}
	result := processViaInterface(p, data)
	util.Sink(result)
}

func interfaceViaFunc002F() {
	data := util.Source()
	var p IDProcessor = IDCleanProcessor{}
	result := processViaInterface(p, data)
	util.Sink(result)
}

func processViaInterface(p IDProcessor, data string) string {
	return p.Process(data)
}
