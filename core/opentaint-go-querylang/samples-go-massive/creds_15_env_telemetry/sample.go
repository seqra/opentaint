package util

import (
	"os"
)

// Sink_SendTelemetry represents a telemetry/analytics call exposing the payload.
func Sink_SendTelemetry(payload string) { _ = payload }

// Positive_telemetry: SESSION_KEY emitted as telemetry payload.
func Positive_telemetry() {
	k := os.Getenv("SESSION_KEY")
	Sink_SendTelemetry("session=" + k)
}

// Negative_telemetry_const: env read but a constant payload sent.
func Negative_telemetry_const() {
	_ = os.Getenv("SESSION_KEY")
	Sink_SendTelemetry("session=anon")
}
