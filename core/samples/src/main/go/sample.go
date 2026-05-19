package test
import "test/util"


func sample() {
	var data = util.Source()
	var other = data
	util.Sink(other)
}

func sampleNonReachable() {
	var data = util.Source()
	var other = "safe"
	util.Sink(other)
	util.Consume(data)
}
