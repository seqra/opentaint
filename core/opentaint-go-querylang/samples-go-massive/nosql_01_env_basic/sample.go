package util

import (
	"fmt"
	"os"
)

// Sink_MongoFind represents a MongoDB Find() call site taking a raw JSON filter.
func Sink_MongoFind(filter string) { _ = filter }

// Positive_env_sprintf: env interpolated into Mongo JSON filter via Sprintf.
func Positive_env_sprintf() {
	u := os.Getenv("MONGO_USER")
	f := fmt.Sprintf(`{"user":"%s"}`, u)
	Sink_MongoFind(f)
}

// Negative_env_const: env read but constant filter sent.
func Negative_env_const() {
	_ = os.Getenv("MONGO_USER")
	Sink_MongoFind(`{"user":"admin"}`)
}
