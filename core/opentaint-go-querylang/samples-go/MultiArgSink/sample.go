package util

// Helpers used by the rule under test.
func Source() string                  { return "tainted" }
func Exec(cmd string, arg string)     { _ = cmd; _ = arg }

// Positive_tainted_arg: tainted value flows into the second arg, which is the sink focus.
func Positive_tainted_arg() {
	Exec("ls", Source())
}

// Negative_tainted_cmd: tainted value lands in arg 0 (cmd), which is NOT the sink focus.
func Negative_tainted_cmd() {
	Exec(Source(), "ls")
}
