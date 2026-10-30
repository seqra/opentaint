package approximation

import (
	"fmt"
	"os"
	"path/filepath"
)

// Models are the models found in the model paths, grouped by the way the analyzer loads them.
type Models struct {
	// JavaClassDirs are the class directories of the Java models.
	JavaClassDirs []string
	// GoModelDirs are the Go model modules.
	GoModelDirs []string
	// Warnings describe the paths, or parts of them, that contribute no models.
	Warnings []string
}

// form is one shape of model input. Each language adds its forms to forms.
type form struct {
	// matches reports whether dir has this form.
	matches func(dir string) bool
	// add records the models of dir. explicit reports that dir is a model path itself rather
	// than a directory found below one. It reports whether dir contributed models.
	add func(r *resolver, dir string, explicit bool) (bool, error)
}

// forms are tried in order on every directory. A directory that has a form is not searched
// further, so the models of a project are never also picked up from its sources or outputs.
var forms = []form{
	{matches: IsProject, add: (*resolver).addJavaProject},
	{matches: isBuiltOutput, add: (*resolver).addJavaBuildOutput},
	{matches: IsGoProject, add: (*resolver).addGoModule},
}

type resolver struct {
	builder Builder
	models  Models
	added   map[string]bool
}

// ResolveAll finds the models in every model path, in the order the paths were given. A model
// path is a model in one of the forms listed in forms, or a directory tree that holds them.
// A directory reached more than once contributes once. The Java class directories must agree
// about every class they share: which copy an analysis reads is not defined, so two different
// copies of one class would leave the result of the scan unpinned.
func ResolveAll(paths []string, builder Builder) (*Models, error) {
	r := &resolver{builder: builder, added: make(map[string]bool)}
	for _, path := range paths {
		if err := r.resolvePath(path); err != nil {
			return nil, err
		}
	}
	if err := checkClasspathAgrees(r.models.JavaClassDirs); err != nil {
		return nil, err
	}
	return &r.models, nil
}

// Resolve finds the models in one model path.
func Resolve(path string, builder Builder) (*Models, error) {
	return ResolveAll([]string{path}, builder)
}

func (r *resolver) resolvePath(path string) error {
	info, err := os.Stat(path)
	if err != nil {
		return fmt.Errorf("model path does not exist: %w", err)
	}
	if !info.IsDir() {
		return fmt.Errorf("model path %s is not a directory", path)
	}

	found, err := r.resolveDir(path, true)
	if err != nil {
		return err
	}
	if !found {
		r.warn(emptyPathWarning(path))
	}
	return nil
}

func (r *resolver) resolveDir(dir string, explicit bool) (bool, error) {
	for _, f := range forms {
		if f.matches(dir) {
			return f.add(r, dir, explicit)
		}
	}

	// os.ReadDir returns entries sorted by name, so the answer does not depend on the
	// order the filesystem happens to hand them back.
	entries, err := os.ReadDir(dir)
	if err != nil {
		return false, fmt.Errorf("failed to read model directory %s: %w", dir, err)
	}
	found := false
	for _, entry := range entries {
		if !entry.IsDir() || skippedDirs[entry.Name()] {
			continue
		}
		nested, err := r.resolveDir(filepath.Join(dir, entry.Name()), false)
		if err != nil {
			return false, err
		}
		found = found || nested
	}
	return found, nil
}

// addJavaProject builds a Java model project when its inputs changed and uses its classes.
func (r *resolver) addJavaProject(dir string, _ bool) (bool, error) {
	classes, err := ensureBuilt(dir, r.builder)
	if err != nil {
		return false, err
	}
	r.addJavaClassDir(classes)
	return true, nil
}

// addJavaBuildOutput uses the classes of a Java model build output.
func (r *resolver) addJavaBuildOutput(dir string, _ bool) (bool, error) {
	r.addJavaClassDir(ClassesDir(dir))
	return true, nil
}

func (r *resolver) addJavaClassDir(dir string) {
	if r.firstTime(dir) {
		r.models.JavaClassDirs = append(r.models.JavaClassDirs, filepath.Clean(dir))
	}
}

// addGoModule uses a Go model module. A Go module with another module path is an error when it
// is the model path itself and is skipped when it is found below one.
func (r *resolver) addGoModule(dir string, explicit bool) (bool, error) {
	modulePath, err := goModulePath(dir)
	if err != nil {
		return false, err
	}
	if !isGoModelModulePath(modulePath) {
		if explicit {
			return false, fmt.Errorf("%s declares Go module %q; a Go model module must be %q",
				dir, modulePath, goModelModulePath)
		}
		r.warn(fmt.Sprintf("Skipping %s: its go.mod declares module %q, not %q",
			dir, modulePath, goModelModulePath))
		return false, nil
	}
	if r.firstTime(dir) {
		r.models.GoModelDirs = append(r.models.GoModelDirs, filepath.Clean(dir))
	}
	return true, nil
}

func (r *resolver) firstTime(dir string) bool {
	dir = filepath.Clean(dir)
	if r.added[dir] {
		return false
	}
	r.added[dir] = true
	return true
}

func (r *resolver) warn(message string) {
	r.models.Warnings = append(r.models.Warnings, message)
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
				return fmt.Errorf(
					"%s is offered with different content by %s and by %s; which one an analysis "+
						"reads is not defined.\nDrop one of the copies, or pass only one of these "+
						"model paths",
					class, previous, dir)
			}
		}
	}
	return nil
}

// emptyPathWarning explains why a path contributes no models.
func emptyPathWarning(path string) string {
	if source, found := firstJavaSource(path); found {
		return fmt.Sprintf(
			"%s holds Java model sources (e.g. %s) but no model project, so they are not used. "+
				"Create one with 'opentaint approximation init <dir> --language java "+
				"--dependency <group:artifact:version>' and move the sources under <dir>/src/main/java",
			path, source,
		)
	}
	return fmt.Sprintf("%s contains no models: no Java model project or build output and no Go model module", path)
}
