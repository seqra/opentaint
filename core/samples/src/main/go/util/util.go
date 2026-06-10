package util

// String Source/Sink (primary)
func Source() string     { return "tainted" }
func Sink(data string)   { Consume(data) }
func Consume(str string) { _ = str }

// Typed Sources for specific test categories
func SourceInt() int         { return 42 }
func SourceFloat() float64   { return 3.14 }
func SourceAny() interface{} { return "tainted" }
func SourceBool() bool       { return true }

// Typed Sinks
func SinkAny(data interface{}) { _ = data }
func SinkInt(data int)         { _ = data }
func SinkBool(data bool)       { _ = data }
func SinkFloat(data float64)   { _ = data }

// Multiple taint mark Sources/Sinks
func SourceA() string   { return "a" }
func SourceB() string   { return "b" }
func SinkA(data string) { _ = data }
func SinkB(data string) { _ = data }

// Pass-through stubs (behavior configured via TaintRules.Pass)
func Passthrough(data string) string          { return data }
func Sanitize(data string) string             { return "clean" }
func Transform(in1 string, in2 string) string { return in2 }

// Collection Sources (whole container tainted via Result position)
func SourceSlice() []string        { return []string{"tainted"} }
func SourceMap() map[string]string { return map[string]string{"k": "tainted"} }

// Global variables for global taint tests
var GlobalTainted string
var GlobalClean string = "safe"
