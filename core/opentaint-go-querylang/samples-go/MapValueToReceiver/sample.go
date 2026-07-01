package util

type Controller struct {
	Data map[string]interface{}
}

func (c *Controller) Serve() {}

func Source() string { return "tainted" }

func Positive_map_value_to_receiver() {
	c := &Controller{Data: map[string]interface{}{"json": Source()}}
	c.Serve()
}

func Negative_const_map() {
	c := &Controller{Data: map[string]interface{}{"json": "safe"}}
	c.Serve()
}
