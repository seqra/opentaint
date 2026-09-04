import Opentaint.Support.Constructive

/-!
# Rebuilding only when something changed

`ensureBuilt` compares a stamp of the model project against the stamp recorded in the
build output and skips the compile when they agree.  That is an optimisation of a simpler
rule — *always compile* — and it is only equivalent to it while the stamp is a function of
everything the compile depends on.

`computeStamp` hashes the files of the project directory: the model sources, the
`build.gradle.kts` that pins the dependencies, and `libs/opentaint-approximations-api.jar`,
which `Prepare` refreshes from the analyzer before the stamp is taken.  It does not cover
the compiler: the CLI's autobuilder is resolved separately, and upgrading it leaves every
cached model build in place.

This file states the equivalence, proves it under the condition that makes it true, and
shows the condition failing for the stamp as shipped.
-/

namespace Opentaint.Approximation

/-- Everything a model build reads.  `sources` stands for the digest `computeStamp`
computes; `toolchain` for the compiler the CLI resolves separately. -/
structure Inputs where
  sources : Nat
  toolchain : Nat
  deriving Repr, DecidableEq

/-- The cache: either nothing has been built, or the recorded output is the output of
compiling exactly these inputs.  Representing the cache by its *inputs* rather than by a
loose stamp/output pair is what makes "the recorded output is genuine" true by
construction, which is the only thing the shipped code guarantees. -/
inductive Cache where
  | empty
  | built (i : Inputs)
  deriving Repr, DecidableEq

/-- The concept: compile, every time. -/
def resolveAlways (compile : Inputs → Nat) (i : Inputs) : Nat × Cache × Nat :=
  (compile i, .built i, 1)

/-- The optimisation: compile only when the stamp moved. -/
def resolveCached {σ} [DecidableEq σ] (stampOf : Inputs → σ) (compile : Inputs → Nat)
    (i : Inputs) : Cache → Nat × Cache × Nat
  | .empty => (compile i, .built i, 1)
  | .built j => if stampOf j = stampOf i then (compile j, .built j, 0)
                else (compile i, .built i, 1)

/-- The condition the optimisation rests on: inputs the stamp cannot tell apart compile to
the same thing. -/
def StampCovers {σ} (stampOf : Inputs → σ) (compile : Inputs → Nat) : Prop :=
  ∀ i j, stampOf i = stampOf j → compile i = compile j

/-- **The optimisation is exact when the stamp covers the compile.** -/
theorem cached_agrees_with_always {σ} [DecidableEq σ]
    (stampOf : Inputs → σ) (compile : Inputs → Nat)
    (h : StampCovers stampOf compile) (i : Inputs) :
    ∀ c : Cache, (resolveCached stampOf compile i c).1 = (resolveAlways compile i).1
  | .empty => rfl
  | .built j => by
      simp only [resolveCached, resolveAlways]
      cases hs : decide (stampOf j = stampOf i) with
      | true =>
          rw [if_pos (of_decide_eq_true hs)]
          exact h j i (of_decide_eq_true hs)
      | false => rw [if_neg (of_decide_eq_false hs)]

/-! ## The stamp as shipped does not cover the compile

`stampSources` is `computeStamp`: a digest of the project's own files, and nothing about
the compiler.  `compileReadsToolchain` is any compile whose result depends on which
compiler ran — which is what upgrading the autobuilder changes. -/

def stampSources (i : Inputs) : Nat := i.sources

def stampSourcesAndToolchain (i : Inputs) : Nat × Nat := (i.sources, i.toolchain)

def compileReadsToolchain (i : Inputs) : Nat := i.sources * 2 + i.toolchain

/-- Same project, upgraded CLI. -/
def before : Inputs := { sources := 7, toolchain := 0 }
def after : Inputs := { sources := 7, toolchain := 1 }

theorem shipped_stamp_does_not_cover :
    stampSources before = stampSources after
      ∧ compileReadsToolchain before ≠ compileReadsToolchain after :=
  ⟨rfl, by decide⟩

/-- **The consequence.**  With the project untouched and the compiler replaced, the cached
resolver hands back the output of the old compiler and the always-compile resolver hands
back the new one. -/
theorem shipped_stamp_serves_a_stale_output :
    (resolveCached stampSources compileReadsToolchain after (.built before)).1
      ≠ (resolveAlways compileReadsToolchain after).1 := by decide

/-- Naming the toolchain in the stamp restores the condition, and with it the
equivalence. -/
theorem full_stamp_covers : StampCovers stampSourcesAndToolchain compileReadsToolchain := by
  intro i j h
  simp only [stampSourcesAndToolchain, Prod.mk.injEq] at h
  simp only [compileReadsToolchain, h.1, h.2]

theorem full_stamp_agrees (i : Inputs) (c : Cache) :
    (resolveCached stampSourcesAndToolchain compileReadsToolchain i c).1
      = (resolveAlways compileReadsToolchain i).1 :=
  cached_agrees_with_always _ _ full_stamp_covers i c

/-! ## The complexity that makes the optimisation worth having

Resolving the same project `k` times in a row: the concept compiles `k` times, the
optimisation compiles once. -/

def compilesAlways (compile : Inputs → Nat) (i : Inputs) : Nat → Cache → Nat
  | 0, _ => 0
  | k + 1, _ =>
      (resolveAlways compile i).2.2
        + compilesAlways compile i k (resolveAlways compile i).2.1

def compilesCached {σ} [DecidableEq σ] (stampOf : Inputs → σ) (compile : Inputs → Nat)
    (i : Inputs) : Nat → Cache → Nat
  | 0, _ => 0
  | k + 1, c =>
      (resolveCached stampOf compile i c).2.2
        + compilesCached stampOf compile i k (resolveCached stampOf compile i c).2.1

theorem always_compiles_every_time (compile : Inputs → Nat) (i : Inputs) :
    ∀ (k : Nat) (c : Cache), compilesAlways compile i k c = k
  | 0, _ => rfl
  | k + 1, c => by
      simp only [compilesAlways, resolveAlways, always_compiles_every_time compile i k]
      omega

theorem cached_stops_compiling {σ} [DecidableEq σ] (stampOf : Inputs → σ)
    (compile : Inputs → Nat) (i : Inputs) :
    ∀ (k : Nat), compilesCached stampOf compile i k (.built i) = 0
  | 0 => rfl
  | k + 1 => by
      simp only [compilesCached, resolveCached]
      simpa using cached_stops_compiling stampOf compile i k

/-- One compile, then none: `k` resolves of an unchanged project cost one compile. -/
theorem cached_compiles_once {σ} [DecidableEq σ] (stampOf : Inputs → σ)
    (compile : Inputs → Nat) (i : Inputs) (k : Nat) :
    compilesCached stampOf compile i (k + 1) .empty = 1 := by
  simp only [compilesCached, resolveCached, cached_stops_compiling stampOf compile i k]

#constructive cached_agrees_with_always shipped_stamp_does_not_cover
#constructive shipped_stamp_serves_a_stale_output full_stamp_covers full_stamp_agrees
#constructive always_compiles_every_time cached_stops_compiling cached_compiles_once

end Opentaint.Approximation
