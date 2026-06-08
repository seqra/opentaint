package util

// Cmd is the type the rule filters on.
type Cmd string

// Helpers used by the rule under test.
func Source() string          { return "tainted" }
func SourceCmd() Cmd           { return Cmd("tainted") }
func Exec(x interface{})       { _ = x }

// Positive_typed_cmd: tainted value is of type util.Cmd — sink fires.
func Positive_typed_cmd() {
	c := SourceCmd()
	Exec(c)
}

//// Negative_typed_string: tainted value is a plain string — sink does NOT fire.
//func Negative_typed_string() {
//	s := Source()
//	Exec(s)
//}
