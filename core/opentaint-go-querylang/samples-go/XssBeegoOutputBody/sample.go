package util

import "strings"

type beegoOutput struct{}

func (o *beegoOutput) Body(content []byte) error { return nil }

type beegoContext struct{ Output *beegoOutput }

type Controller struct {
	Ctx *beegoContext
}

func (c *Controller) GetString(key string) string { return "" }

func (c *Controller) Positive_output_body() {
	param := c.GetString("BenchmarkTest00382")
	bar := strings.ReplaceAll(param, "%s", "a, b")
	c.Ctx.Output.Body([]byte(bar))
}

func (c *Controller) Negative_output_body() {
	bar := strings.ReplaceAll("safe", "%s", "a, b")
	c.Ctx.Output.Body([]byte(bar))
}
