package util

import (
	"os"
)

// Sink_MongoFind represents a MongoDB Find() call site taking a raw JSON filter.
func Sink_MongoFind(filter string) { _ = filter }

// Positive_env_concat: env concatenated directly into Mongo filter.
func Positive_env_concat() {
	id := os.Getenv("MONGO_ID")
	f := `{"_id":"` + id + `"}`
	Sink_MongoFind(f)
}

// Negative_env_concat_const: env read but constant filter.
func Negative_env_concat_const() {
	_ = os.Getenv("MONGO_ID")
	Sink_MongoFind(`{"_id":"00000"}`)
}
