package test

import (
	"test/util"
)

func appendReslice001T() {
	param := util.Source()
	valuesList := []string{"safe", param, "moresafe"}
	valuesList = append(valuesList[:0], valuesList[1:]...)
	out := valuesList[0]
	util.Sink(out)
}

func appendReslice002F() {
	_ = util.Source()
	valuesList := []string{"safe", "alsosafe", "moresafe"}
	valuesList = append(valuesList[:0], valuesList[1:]...)
	out := valuesList[0]
	util.Sink(out)
}

func appendResliceInterproc001T() {
	param := util.Source()
	out := appendResliceHelper(param)
	util.Sink(out)
}

func appendResliceHelper(param string) string {
	bar := ""
	if param != "" {
		valuesList := []string{"safe", param, "moresafe"}
		valuesList = append(valuesList[:0], valuesList[1:]...)
		bar = valuesList[0]
	}
	return bar
}
