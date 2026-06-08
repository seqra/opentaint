package util

import (
	"os"
	"path/filepath"
)

// Positive_walk: tainted env value used as the root for filepath.Walk.
func Positive_walk() {
	root := os.Getenv("WALK_ROOT")
	_ = filepath.Walk(root, func(p string, info os.FileInfo, err error) error {
		return nil
	})
}

// Positive_walk_prefixed: env concatenated with a base dir, then walked.
func Positive_walk_prefixed() {
	sub := os.Getenv("WALK_ROOT")
	_ = filepath.Walk("/var/data/"+sub, func(p string, info os.FileInfo, err error) error {
		return nil
	})
}

// Negative_const: env read but a constant root is walked.
func Negative_const() {
	_ = os.Getenv("WALK_ROOT")
	_ = filepath.Walk("/var/data", func(p string, info os.FileInfo, err error) error {
		return nil
	})
}
