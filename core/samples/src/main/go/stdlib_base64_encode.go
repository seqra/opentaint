package test

import (
	"encoding/base64"
	"test/util"
)

func base64Encode001T() {
	data := util.Source()
	b := base64.StdEncoding.EncodeToString([]byte(data))
	util.Sink(b)
}

func base64Encode002F() {
	_ = util.Source()
	b := base64.StdEncoding.EncodeToString([]byte("safe"))
	util.Sink(b)
}
