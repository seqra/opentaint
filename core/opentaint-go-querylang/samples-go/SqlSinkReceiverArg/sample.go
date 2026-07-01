package sqlrecv

import "database/sql"

func Source() string { return "tainted" }

func Positive_sql_query(db *sql.DB) {
	q := Source()
	rows, _ := db.Query(q)
	_ = rows
}

func Negative_const_query(db *sql.DB) {
	rows, _ := db.Query("select 1")
	_ = rows
}
