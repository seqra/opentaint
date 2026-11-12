package models

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// Models are the dataflow models in the model paths, grouped by the way the analyzer loads them.
type Models struct {
	// JavaClassDirs are the class directories of the Java models.
	JavaClassDirs []string
	// GoModelDirs are the Go model modules.
	GoModelDirs []string
}

// add adds the models of other that m does not hold yet.
func (m *Models) add(other Models, seen map[string]bool) {
	for _, dir := range other.JavaClassDirs {
		if dir = filepath.Clean(dir); !seen[dir] {
			seen[dir] = true
			m.JavaClassDirs = append(m.JavaClassDirs, dir)
		}
	}
	for _, dir := range other.GoModelDirs {
		if dir = filepath.Clean(dir); !seen[dir] {
			seen[dir] = true
			m.GoModelDirs = append(m.GoModelDirs, dir)
		}
	}
}

func (m *Models) empty() bool {
	return len(m.JavaClassDirs) == 0 && len(m.GoModelDirs) == 0
}

// ResolveAll returns the models in every model path, in the order the paths were given. A
// directory reached more than once contributes once, and the Java class directories must agree
// about every class they share: which copy an analysis reads is not defined, so two different
// copies of one class would leave the result of the scan unpinned.
func ResolveAll(paths []string, builder Builder) (*Models, error) {
	var all Models
	seen := make(map[string]bool)
	for _, path := range paths {
		found, err := Resolve(path, builder)
		if err != nil {
			return nil, err
		}
		all.add(*found, seen)
	}
	if err := checkClasspathAgrees(all.JavaClassDirs); err != nil {
		return nil, err
	}
	return &all, nil
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

// Resolve returns the models in one model path. The path can have one of these forms:
//
//  1. A Java model project.
//  2. A Java model build output, as `opentaint compile models` writes it.
//  3. A Go model module: a Go module with the module path opentaint.
//  4. A directory tree that contains these items.
//
// Compiled classes in any other layout are rejected: a build output records the project
// that the models come from, and plain classes do not. A directory with no files holds no
// models, and Resolve returns none for it, so that a directory kept for models can be passed
// before it has any. A directory with files and no models is rejected.
func Resolve(path string, builder Builder) (*Models, error) {
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
func resolve(path string, builder Builder) (*Models, error) {
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

	var found Models
	if err := resolveDir(path, builder, &found); err != nil {
		return nil, err
	}
	if found.empty() && hasFiles(path) {
		return nil, &ProjectNeededError{Path: path, Reason: NoModels}
	}
	return &found, nil
}

// IsEmpty reports whether dir holds no file other than a hidden one or one in a generated
// directory, as a directory kept for models does before it has any.
func IsEmpty(dir string) bool {
	return !hasFiles(dir)
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

func resolveDir(dir string, builder Builder, found *Models) error {
	if IsProject(dir) {
		if builder == nil {
			found.JavaClassDirs = append(found.JavaClassDirs, ClassesDir(BuildDir(dir)))
			return nil
		}
		classes, err := ensureBuilt(dir, builder)
		if err != nil {
			return err
		}
		found.JavaClassDirs = append(found.JavaClassDirs, classes)
		return nil
	}

	if isBuiltOutput(dir) {
		found.JavaClassDirs = append(found.JavaClassDirs, ClassesDir(dir))
		return nil
	}

	if IsGoProject(dir) {
		if err := checkGoModelModule(dir); err != nil {
			return err
		}
		found.GoModelDirs = append(found.GoModelDirs, dir)
		return nil
	}

	// Classes with no model project or build output below them are plain compiled classes,
	// which do not record the project that they come from.
	if facts := scanSubtree(dir); facts.classFiles && !facts.unitSource {
		return &ProjectNeededError{Path: dir, Reason: PlainClasses}
	}

	// os.ReadDir returns entries sorted by name, so the answer does not depend on the
	// order the filesystem happens to hand them back.
	entries, err := os.ReadDir(dir)
	if err != nil {
		return fmt.Errorf("failed to read model directory `%s`: %w", dir, err)
	}

	// Classes beside model projects belong to neither.
	if classFile, found := directClassFile(entries); found {
		return &ProjectNeededError{Path: filepath.Join(dir, classFile), Reason: PlainClasses}
	}

	for _, entry := range entries {
		if !entry.IsDir() || skippedDirs[entry.Name()] {
			continue
		}
		if err := resolveDir(filepath.Join(dir, entry.Name()), builder, found); err != nil {
			return err
		}
	}
	return nil
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
