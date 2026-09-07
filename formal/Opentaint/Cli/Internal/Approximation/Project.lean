import Opentaint.Support.Constructive
import Opentaint.Support.Tree

/-!
# What a directory is

Golden model of `cli/internal/approximation/project.go`: the predicates that classify one
directory, and the walk that answers the two subtree questions the classification needs.

`IsProject` and `isBuiltOutput` are local — a `build.gradle.kts`, or an
`approximation.yaml` next to a `classes/` directory.  `containsClassFiles` is not: it asks
about the whole subtree.  `hasUnitSource` is the question the shipped code never asks, and
`scan` is the single walk that answers both.
-/

namespace Opentaint.Approximation

/-- `IsProject`: a directory with a Gradle build file. -/
def isProject (d : Dir) : Bool := hasFile d .gradleBuild

/-- `isBuiltOutput`: a descriptor next to a `classes/` directory. -/
def isBuiltOutput (d : Dir) : Bool :=
  hasFile d .descriptor && hasSub d .classes

def isClassFile : FileKind → Bool
  | .classFile => true
  | _ => false

/-- `directClassFile`: does this directory hold a compiled class of its own?  Classes
further down belong to whichever unit claims them. -/
def hasDirectClassFile (d : Dir) : Bool := d.files.any isClassFile

/-! The recursive half of `containsClassFiles`: a `.class` file anywhere below a directory
the walk is allowed to enter.  Skipped directories stop the walk. -/
mutual
  def containsBelow : Dir → Bool
    | .mk n fs subs => !isSkipped n && (fs.any isClassFile || containsBelowList subs)

  def containsBelowList : List Dir → Bool
    | [] => false
    | d :: ds => containsBelow d || containsBelowList ds
end

/-- `containsClassFiles`.  The skip list is not applied to the starting directory itself,
matching the `path != dir` guard in the Go walk. -/
def containsClassFiles : Dir → Bool
  | .mk _ fs subs => fs.any isClassFile || containsBelowList subs

/-! Is there a project or a build output at this directory or anywhere the walk can reach
below it?  Equivalently: does anything under here still have to be compiled, or was it
compiled somewhere else.  This is what the shipped resolver does not consult. -/
mutual
  def hasUnitSource : Dir → Bool
    | d@(.mk _ _ subs) => isProject d || isBuiltOutput d || hasUnitSourceList subs

  def hasUnitSourceList : List Dir → Bool
    | [] => false
    | c :: cs => (!isSkipped c.name && hasUnitSource c) || hasUnitSourceList cs
end

/-! ## `scanSubtree`: one walk, both answers

Read literally, the classification needs `containsClassFiles` and `hasUnitSource`, which
is two walks of the same subtree.  `scan` returns both from one. -/

mutual
  def scan : Dir → Bool × Bool
    | d@(.mk _ fs subs) =>
        let below := scanList subs
        (fs.any isClassFile || below.1, isProject d || isBuiltOutput d || below.2)

  def scanList : List Dir → Bool × Bool
    | [] => (false, false)
    | c :: cs =>
        let here := if isSkipped c.name then (false, false) else scan c
        let rest := scanList cs
        (here.1 || rest.1, here.2 || rest.2)
end

mutual
  theorem scan_correct :
      ∀ d : Dir, scan d = (containsClassFiles d, hasUnitSource d)
    | .mk n fs subs => by
        simp only [scan, containsClassFiles, hasUnitSource, scanList_correct subs]

  theorem scanList_correct :
      ∀ ds : List Dir, scanList ds = (containsBelowList ds, hasUnitSourceList ds)
    | [] => rfl
    | c :: cs => by
        cases c with
        | mk n fs subs =>
            simp only [scanList, containsBelowList, hasUnitSourceList, scanList_correct cs,
              containsBelow, Dir.name, scan_correct (.mk n fs subs), containsClassFiles]
            cases hs : isSkipped n with
            | true => simp
            | false => simp
end

/-! ## A subtree with nothing to build contains no project -/

mutual
  theorem no_project_of_no_source (p : Dir.Path) :
      ∀ d : Dir, hasUnitSource d = false →
        (allDirs p d).all (fun e => !isProject e.2) = true
    | .mk n fs subs, h => by
        simp only [hasUnitSource, Bool.or_eq_false_iff] at h
        simp only [allDirs, List.all_cons, Bool.and_eq_true]
        exact ⟨by simp [h.1.1], no_project_of_no_source_list p subs h.2⟩

  theorem no_project_of_no_source_list (p : Dir.Path) :
      ∀ ds : List Dir, hasUnitSourceList ds = false →
        (allDirsList p ds).all (fun e => !isProject e.2) = true
    | [], _ => rfl
    | c :: cs, h => by
        simp only [hasUnitSourceList, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
          Bool.not_eq_false'] at h
        simp only [allDirsList, all_append, Bool.and_eq_true]
        refine ⟨?_, no_project_of_no_source_list p cs h.2⟩
        cases hs : isSkipped c.name with
        | true => simp
        | false =>
            simp only [Bool.false_eq_true, if_false]
            refine no_project_of_no_source (p ++ [c.name]) c ?_
            have := h.1
            rw [hs] at this
            simpa using this
end

#constructive scan_correct scanList_correct
#constructive no_project_of_no_source no_project_of_no_source_list

end Opentaint.Approximation
