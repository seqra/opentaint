package test

import (
	"strconv"
	"test/util"
)

func strconvAtoi001T() {
	data := util.Source()
	id, _ := strconv.Atoi(data)
	util.SinkInt(id)
}

func strconvAtoi002F() {
	_ = util.Source()
	id, _ := strconv.Atoi("safe")
	util.SinkInt(id)
}
