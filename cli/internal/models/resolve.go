package models

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// ResolveAll returns the class directories for every model path, in the order the paths
// were given. A directory reached more than once contributes once, and the directories
// must agree about every class they share: which copy an analysis reads is not defined, so
// two different copies of one class would leave the result of the scan unpinned.
func ResolveAll(paths []string, builder Builder) ([]string, error) {
	var classDirs []string
	resolved := make(map[string]bool)
	for _, path := range paths {
		dirs, err := Resolve(path, builder)
		if err != nil {
			return nil, err
		}
		for _, dir := range dirs {
			dir = filepath.Clean(dir)
			if resolved[dir] {
				continue
			}
			resolved[dir] = true
			classDirs = append(classDirs, dir)
		}
	}
	if err := checkClasspathAgrees(classDirs); err != nil {
		return nil, err
	}
	return classDirs, nil
}

// checkClasspathAgrees rejects class directories that offer one class with different
// content. Identical copies are the ordinary result of overlapping paths and are left
// alone: what has to hold is that the same class is read whichever copy is picked.
func checkClasspathAgrees(classDirs []string) error {
	offeredBy := make(map[string]string)
	for _, dir := range classDirs {
		classes, err := classFilesIn(dir)
		if err != nil {
			return err
		}
		for _, class := range classes {
			previous, offered := offeredBy[class]
			if !offered {
				offeredBy[class] = dir
				continue
			}
			same, err := sameContent(
				filepath.Join(previous, filepath.FromSlash(class)),
				filepath.Join(dir, filepath.FromSlash(class)))
			if err != nil {
				return err
			}
			if !same {
				return fmt.Errorf("`%s` differs in `%s` and `%s`", class, previous, dir)
			}
		}
	}
	return nil
}

// Resolve returns the class directories for one model path.
// The path can have one of these forms:
//
//  1. A model project.
//  2. A model build output, as `opentaint compile models` writes it.
//  3. A directory tree that contains these items.
//
// Compiled classes in any other layout are rejected: a build output records the project
// that the models come from, and plain classes do not. A directory with no files holds no
// models, and Resolve returns none for it, so that a directory kept for models can be passed
// before it has any. A directory with files and no models is rejected.
func Resolve(path string, builder Builder) ([]string, error) {
	return resolve(path, builder)
}

// Check reports what Resolve would reject in a model path without building anything: a path
// that does not exist or that holds no models in a form Resolve takes. A model project counts
// as models here, and whether it compiles is for Resolve to find out. Check names the paths
// below path as joined to it, so a relative path gives relative names.
func Check(path string) error {
	_, err := resolve(path, nil)
	return err
}

// resolve does the work of Resolve. Without a builder it builds nothing, and a model project
// stands for the classes that its build would give.
func resolve(path string, builder Builder) ([]string, error) {
	info, err := os.Stat(path)
	if os.IsNotExist(err) {
		return nil, fmt.Errorf("`%s` does not exist", path)
	}
	if err != nil {
		return nil, fmt.Errorf("failed to access `%s`: %w", path, err)
	}
	if !info.IsDir() {
		return nil, fmt.Errorf("`%s` is not a directory", path)
	}

	classDirs, err := resolveDir(path, builder)
	if err != nil {
		return nil, err
	}
	if len(classDirs) == 0 && hasFiles(path) {
		return nil, &ProjectNeededError{Path: path, Reason: NoModels}
	}
	return classDirs, nil
}

// hasFiles reports whether the tree of dir holds a file other than a hidden one, such as
// .gitkeep, or one in a generated directory.
func hasFiles(dir string) bool {
	found := false
	_ = filepath.WalkDir(dir, func(path string, entry os.DirEntry, err error) error {
		if err != nil {
			// What cannot be read is not known to be empty.
			found = true
			return filepath.SkipAll
		}
		if path == dir {
			return nil
		}
		if strings.HasPrefix(entry.Name(), ".") || skippedDirs[entry.Name()] {
			if entry.IsDir() {
				return filepath.SkipDir
			}
			return nil
		}
		if !entry.IsDir() {
			found = true
			return filepath.SkipAll
		}
		return nil
	})
	return found
}

func resolveDir(dir string, builder Builder) ([]string, error) {
	if IsProject(dir) {
		if builder == nil {
			return []string{ClassesDir(BuildDir(dir))}, nil
		}
		classes, err := ensureBuilt(dir, builder)
		if err != nil {
			return nil, err
		}
		return []string{classes}, nil
	}

	if isBuiltOutput(dir) {
		return []string{ClassesDir(dir)}, nil
	}

	// Classes with no model project or build output below them are plain compiled classes,
	// which do not record the project that they come from.
	if facts := scanSubtree(dir); facts.classFiles && !facts.unitSource {
		return nil, &ProjectNeededError{Path: dir, Reason: PlainClasses}
	}

	// os.ReadDir returns entries sorted by name, so the answer does not depend on the
	// order the filesystem happens to hand them back.
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil, fmt.Errorf("failed to read model directory `%s`: %w", dir, err)
	}

	// Classes beside model projects belong to neither.
	if classFile, found := directClassFile(entries); found {
		return nil, &ProjectNeededError{Path: filepath.Join(dir, classFile), Reason: PlainClasses}
	}

	var classDirs []string
	for _, entry := range entries {
		if !entry.IsDir() || skippedDirs[entry.Name()] {
			continue
		}
		nested, err := resolveDir(filepath.Join(dir, entry.Name()), builder)
		if err != nil {
			return nil, err
		}
		classDirs = append(classDirs, nested...)
	}
	return classDirs, nil
}

// ProjectNeededReason says why a model path needs a model project.
type ProjectNeededReason int

const (
	// NoModels: the path holds no model project or compiled models.
	NoModels ProjectNeededReason = iota
	// PlainClasses: the path holds compiled classes that are not a model build output.
	PlainClasses
)

// ProjectNeededError reports a model path that holds no model project where one is needed.
type ProjectNeededError struct {
	// Path is the model path, or for PlainClasses the directory or class file below it
	// that holds the classes.
	Path   string
	Reason ProjectNeededReason
}

func (e *ProjectNeededError) Error() string {
	if e.Reason == PlainClasses {
		return fmt.Sprintf("`%s` is not a model project or compiled models", e.Path)
	}
	return fmt.Sprintf("`%s` contains no model project or compiled models", e.Path)
}
