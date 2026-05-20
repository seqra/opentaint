package server

import (
	"sync/atomic"
	"testing"
	"time"
)

func TestIdleWatchdog_FiresWhenIdle(t *testing.T) {
	s := NewGoSSAServer("test", "go-test")
	// Make activity old enough to trigger.
	s.lastActivity.Store(time.Now().Add(-time.Hour).UnixNano())

	var called atomic.Bool
	done := make(chan struct{})
	stop := make(chan struct{})
	s.StartIdleWatchdog(50*time.Millisecond, func() {
		if called.CompareAndSwap(false, true) {
			close(done)
		}
	}, stop)
	defer close(stop)

	select {
	case <-done:
	case <-time.After(3 * time.Second):
		t.Fatalf("idle watchdog did not fire")
	}
}

func TestIdleWatchdog_DoesNotFireWhenActive(t *testing.T) {
	s := NewGoSSAServer("test", "go-test")

	var called atomic.Bool
	stop := make(chan struct{})
	defer close(stop)
	s.StartIdleWatchdog(100*time.Millisecond, func() {
		called.Store(true)
	}, stop)

	// Keep bumping activity for ~600ms.
	deadline := time.Now().Add(600 * time.Millisecond)
	for time.Now().Before(deadline) {
		s.touchActivity()
		time.Sleep(20 * time.Millisecond)
	}

	if called.Load() {
		t.Fatalf("idle watchdog fired while activity was ongoing")
	}
}

func TestIdleWatchdog_DisabledByZeroTimeout(t *testing.T) {
	s := NewGoSSAServer("test", "go-test")
	var called atomic.Bool
	stop := make(chan struct{})
	defer close(stop)
	s.StartIdleWatchdog(0, func() { called.Store(true) }, stop)
	time.Sleep(200 * time.Millisecond)
	if called.Load() {
		t.Fatalf("watchdog fired despite zero timeout")
	}
}
