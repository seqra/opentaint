import Opentaint.Support.Constructive
import Opentaint.Cli.Internal.Approximation.Project

/-!
# Resolving an approximation path to compiled model directories

Golden model of `cli/internal/approximation/resolve.go`.  `Resolve` turns one
`--dataflow-approximations` path into the class directories handed to the analyzer.  Four
shapes are documented: a model project, a build output, a compiled class directory, and
*a directory tree that contains these items*.

The fourth shape carries the content.  A tree is classified top-down, and the
classification of a directory is not local: whether it is "a compiled class directory"
depends on what lies below it.  The shipped code answers that with `containsClassFiles`
alone, which is a test of the subtree rather than a classification of the directory.

Three resolvers appear here.  `resolveShipped` is the transcription.  `resolveFixed` is
the design the invariants force.  `resolveFused` is `resolveFixed` costed properly, and is
what the CLI implements.
-/

namespace Opentaint.Approximation

/-- What one directory contributes to the analyzer's approximation classpath. -/
inductive Unit where
  /-- A model project: its sources must be compiled before they contribute anything. -/
  | project (path : Dir.Path)
  /-- A previous build output: its `classes/` directory is used as is. -/
  | output (path : Dir.Path)
  /-- A directory of already-compiled classes, used as a classpath root. -/
  | classes (path : Dir.Path)
  deriving Repr, DecidableEq

/-- The model projects present in a tree: every directory the resolver can reach that
carries a Gradle build file.  These are the ones whose sources still need compiling, so
these are the ones a resolver can silently lose. -/
def projectPathsOf (l : List (Dir.Path × Dir)) : List Dir.Path := pathsWhere isProject l

def projectPaths (p : Dir.Path) (d : Dir) : List Dir.Path := projectPathsOf (allDirs p d)

/-! ## The shipped resolver

A direct transcription of `resolveDir`: project, then build output, then *any class file
anywhere below*, then recurse. -/

mutual
  def resolveShipped (p : Dir.Path) : Dir → List Unit
    | d@(.mk _ _ subs) =>
        if isProject d then [.project p]
        else if isBuiltOutput d then [.output p]
        else if containsClassFiles d then [.classes p]
        else resolveShippedList p subs

  def resolveShippedList (p : Dir.Path) : List Dir → List Unit
    | [] => []
    | c :: cs =>
        (if isSkipped c.name then [] else resolveShipped (p ++ [c.name]) c)
          ++ resolveShippedList p cs
end

/-! ## The intended resolver

Same order, with the class-directory case restricted to what it is meant to mean: a
directory is a classpath root only when nothing below it still needs building. -/

mutual
  def resolveFixed (p : Dir.Path) : Dir → List Unit
    | d@(.mk _ _ subs) =>
        if isProject d then [.project p]
        else if isBuiltOutput d then [.output p]
        else if containsClassFiles d && !hasUnitSource d then [.classes p]
        else resolveFixedList p subs

  def resolveFixedList (p : Dir.Path) : List Dir → List Unit
    | [] => []
    | c :: cs =>
        (if isSkipped c.name then [] else resolveFixed (p ++ [c.name]) c)
          ++ resolveFixedList p cs
end

/-! ## Coverage: when is a project accounted for?

A project unit accounts for the project itself and for anything nested below it — the
project's own build owns its subtree.  A build output does the same.  A *class* unit does
not: it puts already-compiled `.class` files on the classpath, and a project below it is
Java source that nothing ever compiled.  That asymmetry is the whole point. -/

def Unit.covers : Unit → Dir.Path → Bool
  | .project q, p => isPathPrefix q p
  | .output q, p => isPathPrefix q p
  | .classes _, _ => false

/-- A unit puts its whole subtree on the analyzer's classpath, whatever its kind.  This is
the weaker relation the *class* no-loss result is stated against. -/
def Unit.owns : Unit → Dir.Path → Bool
  | .project q, p => isPathPrefix q p
  | .output q, p => isPathPrefix q p
  | .classes q, p => isPathPrefix q p

/-- Every project in the tree is accounted for by some resolved unit. -/
def noProjectLost (resolve : Dir.Path → Dir → List Unit) (d : Dir) : Bool :=
  (projectPaths [] d).all (fun p => (resolve [] d).any (fun u => u.covers p))

/-- Every directory holding compiled classes is claimed by some resolved unit. -/
def noClassLost (resolve : Dir.Path → Dir → List Unit) (d : Dir) : Bool :=
  (pathsWhere hasDirectClassFile (allDirs [] d)).all
    (fun q => (resolve [] d).any (fun u => u.owns q))

theorem projectPathsOf_append (l₁ l₂ : List (Dir.Path × Dir)) :
    projectPathsOf (l₁ ++ l₂) = projectPathsOf l₁ ++ projectPathsOf l₂ :=
  pathsWhere_append isProject l₁ l₂

theorem all_projectPathsOf {f : Dir.Path → Bool} (l : List (Dir.Path × Dir))
    (h : l.all (fun e => f e.1) = true) : (projectPathsOf l).all f = true :=
  all_pathsWhere l h

theorem projectPathsOf_eq_nil (l : List (Dir.Path × Dir))
    (h : l.all (fun e => !isProject e.2) = true) : projectPathsOf l = [] :=
  pathsWhere_eq_nil isProject l h

/-! ## No model project is lost

The statement is generalised over the path prefix so that the induction goes through; the
corollary below is the one the review cares about. -/

mutual
  theorem fixed_covers (p : Dir.Path) :
      ∀ d : Dir,
        (projectPathsOf (allDirs p d)).all
          (fun q => (resolveFixed p d).any (fun u => u.covers q)) = true
    | .mk n fs subs => by
        cases h₁ : isProject (Dir.mk n fs subs) with
        | true =>
            simp only [resolveFixed, h₁, if_true]
            refine all_projectPathsOf (f := fun q => _) _ ?_
            exact all_mono (fun e he => by
              simp only [List.any_cons, List.any_nil, Bool.or_false, Unit.covers]; exact he) _
              (allDirs_below p (.mk n fs subs))
        | false =>
            cases h₂ : isBuiltOutput (Dir.mk n fs subs) with
            | true =>
                simp only [resolveFixed, h₁, Bool.false_eq_true, if_false, h₂, if_true]
                refine all_projectPathsOf (f := fun q => _) _ ?_
                exact all_mono (fun e he => by
                  simp only [List.any_cons, List.any_nil, Bool.or_false, Unit.covers]
                  exact he) _
                  (allDirs_below p (.mk n fs subs))
            | false =>
                cases h₃ : hasUnitSource (Dir.mk n fs subs) with
                | true =>
                    simp only [resolveFixed, h₁, Bool.false_eq_true, if_false, h₂, h₃,
                      Bool.not_true, Bool.and_false]
                    have hnp : projectPathsOf (allDirs p (.mk n fs subs))
                        = projectPathsOf (allDirsList p subs) := by
                      simp only [projectPathsOf, pathsWhere, allDirs, List.filter_cons,
                        h₁, Bool.false_eq_true, if_false]
                    rw [hnp]
                    exact fixed_covers_list p subs
                | false =>
                    have := no_project_of_no_source p (.mk n fs subs) h₃
                    rw [projectPathsOf_eq_nil _ this]
                    rfl

  theorem fixed_covers_list (p : Dir.Path) :
      ∀ ds : List Dir,
        (projectPathsOf (allDirsList p ds)).all
          (fun q => (resolveFixedList p ds).any (fun u => u.covers q)) = true
    | [] => rfl
    | c :: cs => by
        simp only [allDirsList, resolveFixedList, projectPathsOf_append, all_append,
          Bool.and_eq_true]
        constructor
        · cases hs : isSkipped c.name with
          | true => rfl
          | false =>
              simp only [Bool.false_eq_true, if_false]
              refine all_mono (fun q hq => ?_) _ (fixed_covers (p ++ [c.name]) c)
              simp only [any_append, hq, Bool.true_or]
        · refine all_mono (fun q hq => ?_) _ (fixed_covers_list p cs)
          simp only [any_append, hq, Bool.or_true]
end

/-- **No model project is ever silently dropped.**  For every directory tree, every model
project the resolver can reach is covered by a unit the resolver returns: either the
project itself, or an enclosing project or build output that owns it. -/
theorem fixed_loses_nothing (d : Dir) : noProjectLost resolveFixed d = true :=
  fixed_covers [] d

/-! ## The shipped resolver does lose one

`resolveShipped` classifies a directory as "a compiled class directory" as soon as a
`.class` file exists anywhere below it.  When a subtree holds both a stray class file and
a model project, the whole tree collapses to one classpath root: the project's models are
never compiled, the scan runs without them, and nothing says so. -/

/-- A model project: a Gradle build file and a source tree. -/
def modelProject : Dir :=
  .mk (.named 1) [.gradleBuild, .other] [.mk (.named 10) [.other] []]

/-- A directory of classes someone compiled earlier and dropped next to the project. -/
def precompiled : Dir :=
  .mk (.named 2) [] [.mk (.named 20) [.classFile] []]

/-- A previous `opentaint compile approximations` output. -/
def builtOutput : Dir :=
  .mk (.named 2) [.descriptor] [.mk .classes [.classFile] []]

/-- The documented fourth shape: "a directory tree that contains these items". -/
def mixedTree : Dir := .mk (.named 0) [] [modelProject, precompiled]

/-- The same shape with a build output rather than loose classes. -/
def mixedTreeWithOutput : Dir := .mk (.named 0) [] [modelProject, builtOutput]

theorem shipped_collapses_mixed_tree :
    resolveShipped [] mixedTree = [Unit.classes []] := rfl

theorem shipped_collapses_mixed_tree_with_output :
    resolveShipped [] mixedTreeWithOutput = [Unit.classes []] := rfl

/-- **The counterexample.**  A model project present in the tree is accounted for by
nothing the shipped resolver returns. -/
theorem shipped_loses_a_project : noProjectLost resolveShipped mixedTree = false := rfl

theorem shipped_loses_a_project_with_output :
    noProjectLost resolveShipped mixedTreeWithOutput = false := rfl

theorem fixed_separates_mixed_tree :
    resolveFixed [] mixedTree = [Unit.project [.named 1], Unit.classes [.named 2]] := rfl

theorem fixed_separates_mixed_tree_with_output :
    resolveFixed [] mixedTreeWithOutput
      = [Unit.project [.named 1], Unit.output [.named 2]] := rfl

theorem fixed_keeps_the_project : noProjectLost resolveFixed mixedTree = true :=
  fixed_loses_nothing _

/-! ## The guard changes nothing that already worked

`classDirsAreLeaves` is the precondition under which the shipped shortcut *is* a correct
classification: wherever it decides "class directory", nothing below still needs building.
Under it the two resolvers are indistinguishable, so the guard is a repair rather than a
behaviour change. -/

mutual
  def classDirsAreLeaves : Dir → Bool
    | d@(.mk _ _ subs) =>
        if isProject d then true
        else if isBuiltOutput d then true
        else if containsClassFiles d then !hasUnitSource d
        else classDirsAreLeavesList subs

  def classDirsAreLeavesList : List Dir → Bool
    | [] => true
    | c :: cs => (isSkipped c.name || classDirsAreLeaves c) && classDirsAreLeavesList cs
end

mutual
  theorem shipped_eq_fixed (p : Dir.Path) :
      ∀ d : Dir, classDirsAreLeaves d = true → resolveShipped p d = resolveFixed p d
    | .mk n fs subs, h => by
        cases h₁ : isProject (Dir.mk n fs subs) with
        | true => simp only [resolveShipped, resolveFixed, h₁, if_true]
        | false =>
            cases h₂ : isBuiltOutput (Dir.mk n fs subs) with
            | true =>
                simp only [resolveShipped, resolveFixed, h₁, Bool.false_eq_true, if_false,
                  h₂, if_true]
            | false =>
                cases h₃ : containsClassFiles (Dir.mk n fs subs) with
                | true =>
                    have hs : hasUnitSource (Dir.mk n fs subs) = false := by
                      simp only [classDirsAreLeaves, h₁, Bool.false_eq_true, if_false, h₂,
                        h₃, if_true, Bool.not_eq_true'] at h
                      exact h
                    simp only [resolveShipped, resolveFixed, h₁, Bool.false_eq_true,
                      if_false, h₂, h₃, if_true, hs, Bool.not_false, Bool.and_true]
                | false =>
                    have hrec : classDirsAreLeavesList subs = true := by
                      simp only [classDirsAreLeaves, h₁, Bool.false_eq_true, if_false, h₂,
                        h₃] at h
                      exact h
                    simp only [resolveShipped, resolveFixed, h₁, Bool.false_eq_true,
                      if_false, h₂, h₃, Bool.false_and, if_false]
                    exact shipped_eq_fixed_list p subs hrec

  theorem shipped_eq_fixed_list (p : Dir.Path) :
      ∀ ds : List Dir, classDirsAreLeavesList ds = true →
        resolveShippedList p ds = resolveFixedList p ds
    | [], _ => rfl
    | c :: cs, h => by
        simp only [classDirsAreLeavesList, Bool.and_eq_true, Bool.or_eq_true] at h
        simp only [resolveShippedList, resolveFixedList]
        have htail := shipped_eq_fixed_list p cs h.2
        cases hs : isSkipped c.name with
        | true => simp [htail]
        | false =>
            have hc : classDirsAreLeaves c = true := by
              cases h.1 with
              | inl hskip => rw [hs] at hskip; exact absurd hskip (by simp)
              | inr hleaf => exact hleaf
            simp only [Bool.false_eq_true, if_false, shipped_eq_fixed (p ++ [c.name]) c hc,
              htail]
end

theorem shipped_agrees_when_class_dirs_are_leaves (d : Dir)
    (h : classDirsAreLeaves d = true) : resolveShipped [] d = resolveFixed [] d :=
  shipped_eq_fixed [] d h

/-- And the witness is outside that precondition — the two results do not overlap. -/
theorem mixedTree_is_not_leaf_shaped : classDirsAreLeaves mixedTree = false := rfl

/-! ## Compiled classes can be lost too

`fixed_loses_nothing` says nothing about compiled classes, and there the guard opens a
second, smaller hole: a directory that holds `.class` files *directly* and also holds a
model project below it is neither a classpath root (something below it still needs
building) nor a pure container (its own class files belong to no unit).

There is no classification that saves them: putting the directory on the classpath
swallows the project's sources, and recursing drops the classes.  The layout is ambiguous,
and the honest answer is to say so rather than to silently pick a side.  `unambiguous` is
the condition under which no side has to be picked; the CLI validates it and names the
directory when it fails. -/

mutual
  def unambiguous : Dir → Bool
    | d@(.mk _ fs subs) =>
        if isProject d then true
        else if isBuiltOutput d then true
        else if containsClassFiles d && !hasUnitSource d then true
        else !(fs.any isClassFile) && unambiguousList subs

  def unambiguousList : List Dir → Bool
    | [] => true
    | c :: cs => (isSkipped c.name || unambiguous c) && unambiguousList cs
end

mutual
  theorem fixed_owns_classes (p : Dir.Path) :
      ∀ d : Dir, unambiguous d = true →
        (pathsWhere hasDirectClassFile (allDirs p d)).all
          (fun q => (resolveFixed p d).any (fun u => u.owns q)) = true
    | .mk n fs subs, h => by
        cases h₁ : isProject (Dir.mk n fs subs) with
        | true =>
            simp only [resolveFixed, h₁, if_true]
            refine all_pathsWhere _ ?_
            exact all_mono (fun e he => by
              simp only [List.any_cons, List.any_nil, Bool.or_false, Unit.owns]; exact he) _
              (allDirs_below p (.mk n fs subs))
        | false =>
            cases h₂ : isBuiltOutput (Dir.mk n fs subs) with
            | true =>
                simp only [resolveFixed, h₁, Bool.false_eq_true, if_false, h₂, if_true]
                refine all_pathsWhere _ ?_
                exact all_mono (fun e he => by
                  simp only [List.any_cons, List.any_nil, Bool.or_false, Unit.owns]
                  exact he) _
                  (allDirs_below p (.mk n fs subs))
            | false =>
                cases h₃ : (containsClassFiles (Dir.mk n fs subs)
                    && !hasUnitSource (Dir.mk n fs subs)) with
                | true =>
                    simp only [resolveFixed, h₁, Bool.false_eq_true, if_false, h₂, h₃,
                      if_true]
                    refine all_pathsWhere _ ?_
                    exact all_mono (fun e he => by
                      simp only [List.any_cons, List.any_nil, Bool.or_false, Unit.owns]
                      exact he) _
                      (allDirs_below p (.mk n fs subs))
                | false =>
                    simp only [unambiguous, h₁, Bool.false_eq_true, if_false, h₂, h₃,
                      Bool.and_eq_true, Bool.not_eq_true'] at h
                    simp only [resolveFixed, h₁, Bool.false_eq_true, if_false, h₂, h₃,
                      if_false]
                    have hnp : pathsWhere hasDirectClassFile (allDirs p (.mk n fs subs))
                        = pathsWhere hasDirectClassFile (allDirsList p subs) := by
                      simp only [pathsWhere, allDirs, List.filter_cons, hasDirectClassFile,
                        Dir.files, h.1, Bool.false_eq_true, if_false]
                    rw [hnp]
                    exact fixed_owns_classes_list p subs h.2

  theorem fixed_owns_classes_list (p : Dir.Path) :
      ∀ ds : List Dir, unambiguousList ds = true →
        (pathsWhere hasDirectClassFile (allDirsList p ds)).all
          (fun q => (resolveFixedList p ds).any (fun u => u.owns q)) = true
    | [], _ => rfl
    | c :: cs, h => by
        simp only [unambiguousList, Bool.and_eq_true, Bool.or_eq_true] at h
        simp only [allDirsList, resolveFixedList, pathsWhere_append, all_append,
          Bool.and_eq_true]
        constructor
        · cases hs : isSkipped c.name with
          | true => rfl
          | false =>
              have hc : unambiguous c = true := by
                cases h.1 with
                | inl hskip => rw [hs] at hskip; exact absurd hskip (by simp)
                | inr hu => exact hu
              simp only [Bool.false_eq_true, if_false]
              refine all_mono (fun q hq => ?_) _ (fixed_owns_classes (p ++ [c.name]) c hc)
              simp only [any_append, hq, Bool.true_or]
        · refine all_mono (fun q hq => ?_) _ (fixed_owns_classes_list p cs h.2)
          simp only [any_append, hq, Bool.or_true]
end

/-- **Nothing is lost on an unambiguous layout.**  With `fixed_loses_nothing`, which needs
no precondition, this is the full no-loss statement for the resolver. -/
theorem fixed_loses_no_classes (d : Dir) (h : unambiguous d = true) :
    noClassLost resolveFixed d = true := fixed_owns_classes [] d h

/-- A class file next to a model project: the resolver builds the project and the class
file reaches no classpath.  No guard fixes this — the CLI reports it. -/
def ambiguousTree : Dir := .mk (.named 0) [.classFile] [modelProject]

theorem ambiguousTree_is_ambiguous : unambiguous ambiguousTree = false := rfl

theorem ambiguous_tree_drops_a_class :
    noClassLost resolveFixed ambiguousTree = false := rfl

theorem ambiguous_tree_still_keeps_the_project :
    noProjectLost resolveFixed ambiguousTree = true := fixed_loses_nothing _

/-- The mixed tree is unambiguous: the repaired resolver handles it with no diagnostic,
which is what makes it a repair rather than a new error. -/
theorem mixedTree_is_unambiguous : unambiguous mixedTree = true := rfl

theorem mixedTree_keeps_its_classes : noClassLost resolveFixed mixedTree = true :=
  fixed_loses_no_classes _ mixedTree_is_unambiguous

/-! ## One walk instead of two

`resolveFixed` states the classification the obvious way, which reads as two walks of the
same subtree at every candidate directory.  `resolveFused` uses `scan`, and answers
identically on every tree — so the walk count is the only difference between them. -/

mutual
  def resolveFused (p : Dir.Path) : Dir → List Unit
    | d@(.mk _ _ subs) =>
        if isProject d then [.project p]
        else if isBuiltOutput d then [.output p]
        else
          let facts := scan d
          if facts.1 && !facts.2 then [.classes p]
          else resolveFusedList p subs

  def resolveFusedList (p : Dir.Path) : List Dir → List Unit
    | [] => []
    | c :: cs =>
        (if isSkipped c.name then [] else resolveFused (p ++ [c.name]) c)
          ++ resolveFusedList p cs
end

mutual
  theorem fused_eq_fixed (p : Dir.Path) :
      ∀ d : Dir, resolveFused p d = resolveFixed p d
    | .mk n fs subs => by
        simp only [resolveFused, resolveFixed, scan_correct (.mk n fs subs)]
        cases h₁ : isProject (Dir.mk n fs subs) with
        | true => simp
        | false =>
            cases h₂ : isBuiltOutput (Dir.mk n fs subs) with
            | true => simp
            | false =>
                simp only [Bool.false_eq_true, if_false]
                cases h₃ : (containsClassFiles (Dir.mk n fs subs)
                    && !hasUnitSource (Dir.mk n fs subs)) with
                | true => simp
                | false => simp only [Bool.false_eq_true, if_false,
                    fused_eq_fixed_list p subs]

  theorem fused_eq_fixed_list (p : Dir.Path) :
      ∀ ds : List Dir, resolveFusedList p ds = resolveFixedList p ds
    | [] => rfl
    | c :: cs => by
        simp only [resolveFusedList, resolveFixedList, fused_eq_fixed_list p cs]
        cases hs : isSkipped c.name with
        | true => simp
        | false => simp only [Bool.false_eq_true, if_false, fused_eq_fixed (p ++ [c.name]) c]
end

/-- **The optimisation is exact.**  Fusing the two subtree walks into one changes no
answer, on any tree. -/
theorem fused_resolves_identically (d : Dir) :
    resolveFused [] d = resolveFixed [] d := fused_eq_fixed [] d

/-! `walks` counts full subtree traversals launched at one directory: `containsClassFiles`
and `hasUnitSource` are one each, `scan` is one for both.  `Bool.and` short-circuits, so
the second walk of the unfused form is only paid when the first succeeds — which is
exactly the case the guard exists for. -/

def walksFixed (d : Dir) : Nat :=
  if isProject d || isBuiltOutput d then 0
  else if containsClassFiles d then 2 else 1

def walksFused (d : Dir) : Nat :=
  if isProject d || isBuiltOutput d then 0 else 1

theorem fused_never_walks_more (d : Dir) : walksFused d ≤ walksFixed d := by
  simp only [walksFixed, walksFused]
  cases h : (isProject d || isBuiltOutput d) with
  | true => simp
  | false =>
      simp only [Bool.false_eq_true, if_false]
      cases containsClassFiles d <;> simp

/-- Wherever the guard is actually reached, the unfused form walks the subtree twice and
the fused form once. -/
theorem guard_costs_a_second_walk (d : Dir)
    (h₁ : isProject d = false) (h₂ : isBuiltOutput d = false)
    (h₃ : containsClassFiles d = true) :
    walksFixed d = 2 ∧ walksFused d = 1 := by
  unfold walksFixed walksFused
  simp [h₁, h₂, h₃]

theorem precompiled_pays_twice :
    walksFixed precompiled = 2 ∧ walksFused precompiled = 1 := by
  constructor <;> decide

#constructive fixed_covers fixed_covers_list fixed_loses_nothing
#constructive shipped_collapses_mixed_tree shipped_loses_a_project
#constructive shipped_loses_a_project_with_output fixed_separates_mixed_tree
#constructive shipped_eq_fixed shipped_eq_fixed_list
#constructive shipped_agrees_when_class_dirs_are_leaves mixedTree_is_not_leaf_shaped
#constructive fixed_owns_classes fixed_owns_classes_list fixed_loses_no_classes
#constructive ambiguousTree_is_ambiguous ambiguous_tree_drops_a_class
#constructive mixedTree_is_unambiguous mixedTree_keeps_its_classes
#constructive fused_eq_fixed fused_eq_fixed_list fused_resolves_identically
#constructive fused_never_walks_more guard_costs_a_second_walk

end Opentaint.Approximation
