import Opentaint.Support.Prelude

/-!
# The directory tree an approximation path is resolved against

`opentaint scan --dataflow-approximations <path>` is handed a directory and must decide
what compiled model classes it contributes.  Everything the resolver looks at is a
*name*: whether a directory holds a `build.gradle.kts`, an `approximation.yaml`, a
`classes/` subdirectory, or a `.class` file somewhere below it.  So the abstraction is a
rose tree of directories carrying only names — file contents are absent by design,
because the resolver never reads them.

## The name abstraction, and why it is sound

Names are not modelled as strings.  The resolver asks exactly four questions of a name:

* is this file `build.gradle.kts`?            (`IsProject`)
* is this file `approximation.yaml`?          (`isBuiltOutput`)
* does this file end in `.class`?             (`containsClassFiles`)
* is this directory `classes`, or on the skip list `{.opentaint, build, .gradle, .git}`?

Nothing else about a name reaches a decision — two names that answer all four the same
way are interchangeable to the resolver.  `FileKind` and `DirName` below are the quotient
by that equivalence, so a property proved here holds of every string instantiation.  The
quotient is well defined because the classes do not overlap: `classes` is not on the skip
list, and the two marker files are distinct from each other and from any `*.class`.

This file has no counterpart in the CLI: it models the filesystem the CLI walks, not code
the CLI contains.
-/

namespace Opentaint.Approximation

/-- The only distinctions the resolver draws between file names. -/
inductive FileKind where
  /-- `build.gradle.kts` — marks a model project. -/
  | gradleBuild
  /-- `approximation.yaml` — marks a compiled build output. -/
  | descriptor
  /-- `*.class` — a compiled class. -/
  | classFile
  /-- Anything else: sources, jars, READMEs.  Invisible to the resolver. -/
  | other
  deriving Repr, DecidableEq, Inhabited

/-- The only distinctions the resolver draws between directory names.  Names outside the
two special classes matter only for telling siblings apart, so they are numbered. -/
inductive DirName where
  /-- One of `.opentaint`, `build`, `.gradle`, `.git`: the walk never enters it. -/
  | skipped
  /-- `classes`, the directory a build output keeps its output in. -/
  | classes
  /-- Any other name. -/
  | named (id : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A directory: its name, the files directly in it, and its subdirectories. -/
inductive Dir where
  | mk (name : DirName) (files : List FileKind) (subs : List Dir)
  deriving Repr, Inhabited

namespace Dir

def name : Dir → DirName
  | .mk n _ _ => n

def files : Dir → List FileKind
  | .mk _ f _ => f

def subs : Dir → List Dir
  | .mk _ _ s => s

/-- A path from the tree root to a directory, as the names taken.  `[]` is the directory
the user passed on the command line. -/
abbrev Path := List DirName

end Dir

/-- The walk refuses to enter build output and version-control directories. -/
def isSkipped : DirName → Bool
  | .skipped => true
  | _ => false

def hasFile (d : Dir) (f : FileKind) : Bool := d.files.contains f

def hasSub (d : Dir) (n : DirName) : Bool := d.subs.any (fun s => s.name == n)

/-! ## Where the directories are

`allDirs` enumerates the directories a walk from `p` may reach: everything below it except
what the skip list cuts off.  A project under `build/` is invisible to the CLI by design,
and is invisible here for the same reason. -/

mutual
  def allDirs (p : Dir.Path) : Dir → List (Dir.Path × Dir)
    | d@(.mk _ _ subs) => (p, d) :: allDirsList p subs

  def allDirsList (p : Dir.Path) : List Dir → List (Dir.Path × Dir)
    | [] => []
    | c :: cs =>
        (if isSkipped c.name then [] else allDirs (p ++ [c.name]) c) ++ allDirsList p cs
end

/-- The paths of the reachable directories satisfying a predicate. -/
def pathsWhere (pred : Dir → Bool) (l : List (Dir.Path × Dir)) : List Dir.Path :=
  (l.filter (fun e => pred e.2)).map (·.1)

/-! ## Path prefixes

One path lies under another.  This is how a resolved unit is related to the directories it
claims. -/

def isPathPrefix : Dir.Path → Dir.Path → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && isPathPrefix as bs

/-- `beq_self_eq_true` is stated for `[ReflBEq]` and core's instances reach it through
classical lemmas; `formal/` refuses `Classical.choice`, and decidability gives the same
fact constructively. -/
theorem beq_name_self (a : DirName) : (a == a) = true := decide_eq_true rfl

theorem isPathPrefix_refl : ∀ p : Dir.Path, isPathPrefix p p = true
  | [] => rfl
  | a :: as => by
      simp only [isPathPrefix, beq_name_self, Bool.true_and, isPathPrefix_refl as]

theorem isPathPrefix_append : ∀ (p x : Dir.Path), isPathPrefix p (p ++ x) = true
  | [], _ => rfl
  | a :: as, x => by
      simp only [List.cons_append, isPathPrefix, beq_name_self, Bool.true_and,
        isPathPrefix_append as x]

theorem isPathPrefix_trans :
    ∀ a b c : Dir.Path, isPathPrefix a b = true → isPathPrefix b c = true →
      isPathPrefix a c = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [isPathPrefix] at h
  | _ :: _, _ :: _, [], _, h => by simp [isPathPrefix] at h
  | x :: xs, y :: ys, z :: zs, h₁, h₂ => by
      simp only [isPathPrefix, Bool.and_eq_true, beq_iff_eq] at h₁ h₂ ⊢
      exact ⟨h₁.1.trans h₂.1, isPathPrefix_trans xs ys zs h₁.2 h₂.2⟩

/-! ## Every directory `allDirs` reports sits below the path it started from -/

mutual
  theorem allDirs_below (p : Dir.Path) :
      ∀ d : Dir, (allDirs p d).all (fun e => isPathPrefix p e.1) = true
    | .mk n fs subs => by
        simp only [allDirs, List.all_cons, Bool.and_eq_true]
        exact ⟨isPathPrefix_refl p, allDirsList_below p subs⟩

  theorem allDirsList_below (p : Dir.Path) :
      ∀ ds : List Dir, (allDirsList p ds).all (fun e => isPathPrefix p e.1) = true
    | [] => rfl
    | c :: cs => by
        simp only [allDirsList, all_append, Bool.and_eq_true]
        refine ⟨?_, allDirsList_below p cs⟩
        cases hs : isSkipped c.name with
        | true => simp
        | false =>
            simp only [Bool.false_eq_true, if_false]
            refine all_mono (fun e he => ?_) _ (allDirs_below (p ++ [c.name]) c)
            exact isPathPrefix_trans p (p ++ [c.name]) e.1 (isPathPrefix_append p [c.name]) he
end

/-! ## `pathsWhere` under the list operations the recursion produces -/

theorem pathsWhere_append (pred : Dir → Bool) :
    ∀ l₁ l₂ : List (Dir.Path × Dir),
      pathsWhere pred (l₁ ++ l₂) = pathsWhere pred l₁ ++ pathsWhere pred l₂ := by
  intro l₁ l₂
  simp [pathsWhere, List.filter_append, List.map_append]

theorem all_pathsWhere {pred : Dir → Bool} {f : Dir.Path → Bool} :
    ∀ l : List (Dir.Path × Dir), l.all (fun e => f e.1) = true →
      (pathsWhere pred l).all f = true
  | [], _ => rfl
  | e :: es, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      cases hp : pred e.2 with
      | true =>
          simp only [pathsWhere, List.filter_cons, hp, if_true, List.map_cons,
            List.all_cons, Bool.and_eq_true]
          exact ⟨h.1, all_pathsWhere es h.2⟩
      | false =>
          simpa only [pathsWhere, List.filter_cons, hp, Bool.false_eq_true, if_false] using
            all_pathsWhere es h.2

theorem pathsWhere_eq_nil (pred : Dir → Bool) :
    ∀ l : List (Dir.Path × Dir), l.all (fun e => !pred e.2) = true →
      pathsWhere pred l = []
  | [], _ => rfl
  | e :: es, h => by
      simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
      simpa only [pathsWhere, List.filter_cons, h.1, Bool.false_eq_true, if_false] using
        pathsWhere_eq_nil pred es h.2

#constructive beq_name_self isPathPrefix_refl isPathPrefix_append isPathPrefix_trans
#constructive allDirs_below allDirsList_below
#constructive pathsWhere_append all_pathsWhere pathsWhere_eq_nil

end Opentaint.Approximation
