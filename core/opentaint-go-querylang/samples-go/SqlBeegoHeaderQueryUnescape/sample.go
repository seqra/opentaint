package util

import (
	"database/sql"
	"fmt"
	"net/url"
)

type beegoInput struct{}

func (i *beegoInput) Header(k string) string { return "" }

type beegoContext struct{ Input *beegoInput }

type Controller struct{ Ctx *beegoContext }

func (c *Controller) Positive_beego_header_sql(db *sql.DB) {
	param := c.Ctx.Input.Header("X-Test")
	if param != "" {
		param, _ = url.QueryUnescape(param)
	}
	sqlStr := fmt.Sprintf("SELECT * from USERS where NAME='%s'", param)
	row := db.QueryRow(sqlStr)
	_ = row
}

func (c *Controller) Negative_const_sql(db *sql.DB) {
	_ = c
	sqlStr := "SELECT * from USERS where NAME='foo'"
	row := db.QueryRow(sqlStr)
	_ = row
}
