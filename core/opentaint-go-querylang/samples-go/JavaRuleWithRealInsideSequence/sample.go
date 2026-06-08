package util

// Go port of example.RuleWithRealInsideSequence. Java rule chains two
// pattern-insides on an ObjectMapper: `new ObjectMapper(...)` then
// `enableDefaultTyping()` before `readValue`. Recast in Go as
// EnableDefaultTyping returning the OM (source) → ReadValue (sink).
func NewOM() string                  { return "om" }
func EnableDefaultTyping(om string) string { return om }
func ReadValue(om string)            { _ = om }

// Positive_simple: enable typing then read.
func Positive_simple() {
	om := NewOM()
	tainted := EnableDefaultTyping(om)
	ReadValue(tainted)
}

// Negative_no_enable: no EnableDefaultTyping called.
func Negative_no_enable() {
	om := NewOM()
	ReadValue(om)
}
