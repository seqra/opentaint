package main

import (
	"io"
	"sync/atomic"
	"testing"
	"time"
)

func TestWatchStdinAndExit_OnEOF(t *testing.T) {
	pr, pw := io.Pipe()
	var called atomic.Bool
	done := make(chan struct{})
	go func() {
		watchStdinAndExit(pr, func() {
			called.Store(true)
			close(done)
		})
	}()

	// Simulate parent JVM dying: close the write end of the pipe.
	if err := pw.Close(); err != nil {
		t.Fatalf("close pipe: %v", err)
	}

	select {
	case <-done:
	case <-time.After(2 * time.Second):
		t.Fatalf("shutdown not invoked after stdin EOF")
	}
	if !called.Load() {
		t.Fatalf("shutdown callback not called")
	}
}

func TestWatchStdinAndExit_OnReadError(t *testing.T) {
	pr, pw := io.Pipe()
	var called atomic.Bool
	done := make(chan struct{})
	go func() {
		watchStdinAndExit(pr, func() {
			called.Store(true)
			close(done)
		})
	}()
	// Inject a non-EOF error.
	_ = pw.CloseWithError(io.ErrClosedPipe)
	select {
	case <-done:
	case <-time.After(2 * time.Second):
		t.Fatalf("shutdown not invoked on read error")
	}
	if !called.Load() {
		t.Fatalf("shutdown callback not called")
	}
}
