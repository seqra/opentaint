import Opentaint.Support.Constructive

/-!
# Publishing a build output

`build` in `cli/internal/approximation/build.go` assembles a build output in a staging
directory and then moves it into place.  Two things about that protocol are observable to
anybody else looking at the output directory — another `opentaint scan` on the same
project, or a `compile approximations` running beside it:

* the staging path is derived from the output path alone, so two builders share it;
* the output directory is deleted and then renamed over, so it is observable half-deleted
  while still passing the `isBuiltOutput` test a reader uses.

This file models the protocol as interleaved atomic steps.  The abstraction keeps only
what a reader can distinguish: whether the directory exists, whose compiled classes are in
it, and whether a descriptor has been written — which is exactly what `isBuiltOutput`
looks at.
-/

namespace Opentaint.Approximation

/-- Two concurrent builders of the same output.  Two is enough: the defect is a race
between any pair, and the repair is per-builder isolation. -/
inductive Bldr where
  | one
  | two
  deriving Repr, DecidableEq

/-- A directory as a reader can see it. -/
inductive Slot where
  /-- No directory at this path. -/
  | absent
  /-- A directory holding the classes contributed by the listed builders, and, once a
  descriptor has been written, the builder that wrote it. -/
  | dir (classes : List Bldr) (sealed : Option Bldr)
  deriving Repr, DecidableEq

/-- `isBuiltOutput`: a descriptor next to a classes directory.  This is the whole of what
a reader checks before handing a directory to the analyzer. -/
def Slot.readable : Slot → Bool
  | .absent => false
  | .dir _ none => false
  | .dir _ (some _) => true

/-- A readable output is *sound* when everything in it came from the build that sealed it.
An output carrying two builders' classes is not: part of it is one compile of the models
and part another, under a descriptor and a stamp that name only one. -/
def Slot.sound : Slot → Bool
  | .absent => true
  | .dir _ none => true
  | .dir classes (some b) => classes.all (fun c => c == b)

def Slot.addClass (b : Bldr) : Slot → Slot
  | .absent => .absent
  | .dir cs s => .dir (cs ++ [b]) s

def Slot.seal (b : Bldr) : Slot → Slot
  | .absent => .absent
  | .dir cs _ => .dir cs (some b)

/-! ## Protocol A: one staging path, output deleted before the rename

`staging := outputDir + ".incomplete"`, so every builder of the same output uses the same
directory. -/

structure StateA where
  out : Slot
  stg : Slot
  deriving Repr, DecidableEq

inductive ActA where
  /-- `os.RemoveAll(staging)` then `os.MkdirAll(staging/classes)`. -/
  | reset (b : Bldr)
  /-- `collectClasses` copies this builder's classes into the staging directory. -/
  | copy (b : Bldr)
  /-- `writeDescriptor` and `writeStamp`. -/
  | sealDir (b : Bldr)
  /-- `replaceDir` step one: `os.RemoveAll(outputDir)`. -/
  | removeOut
  /-- `replaceDir` step two: `os.Rename(staging, outputDir)`. -/
  | renameIn
  deriving Repr

def stepA (s : StateA) : ActA → StateA
  | .reset _ => { s with stg := .dir [] none }
  | .copy b => { s with stg := s.stg.addClass b }
  | .sealDir b => { s with stg := s.stg.seal b }
  | .removeOut => { s with out := .absent }
  | .renameIn => { out := s.stg, stg := .absent }

def runA (s : StateA) : List ActA → StateA
  | [] => s
  | a :: as => runA (stepA s a) as

def initA : StateA := { out := .absent, stg := .absent }

/-- An interleaving the shipped protocol allows: builder one resets and starts copying,
builder two resets — deleting builder one's work — and copies, builder one copies the
rest of its classes into what is now builder two's staging directory, and builder two
seals and publishes. -/
def raceA : List ActA :=
  [.reset .one, .copy .one, .reset .two, .copy .two, .copy .one, .sealDir .two,
   .removeOut, .renameIn]

/-- **The shipped protocol can publish a mixed output.**  The result passes the reader's
test, so the analyzer uses it, and it holds classes from two different compiles under a
descriptor and a stamp naming one of them.  The stamp is the damaging part: the mixture is
recorded as up to date and is never rebuilt. -/
theorem raceA_publishes_a_mixture :
    (runA initA raceA).out = .dir [.two, .one] (some .two) := rfl

theorem raceA_output_is_readable : (runA initA raceA).out.readable = true := rfl

theorem raceA_output_is_not_sound : (runA initA raceA).out.sound = false := rfl

/-! ## Protocol B: a staging path per builder, old output renamed aside

Each builder assembles under a path only it uses, and publishing renames the previous
output away in one step before renaming the new one in.  Both renames are atomic, so a
reader sees the old output, the new output, or nothing. -/

structure StateB where
  out : Slot
  stg1 : Slot
  stg2 : Slot
  deriving Repr, DecidableEq

inductive ActB where
  | reset (b : Bldr)
  | copy (b : Bldr)
  | sealDir (b : Bldr)
  /-- `os.Rename(outputDir, aside)`: the old output leaves in one step. -/
  | moveOutAside
  /-- `os.Rename(staging, outputDir)`: the new output arrives in one step. -/
  | renameIn (b : Bldr)
  deriving Repr

/-- The staging path carries the builder's identity, so a builder only ever reads and
writes its own slot. -/
def StateB.stg : StateB → Bldr → Slot
  | s, .one => s.stg1
  | s, .two => s.stg2

def StateB.withStg : StateB → Bldr → Slot → StateB
  | s, .one, v => { s with stg1 := v }
  | s, .two, v => { s with stg2 := v }

def stepB (s : StateB) : ActB → StateB
  | .reset b => s.withStg b (.dir [] none)
  | .copy b => s.withStg b ((s.stg b).addClass b)
  | .sealDir b => s.withStg b ((s.stg b).seal b)
  | .moveOutAside => { s with out := .absent }
  | .renameIn b => { s.withStg b .absent with out := s.stg b }

def runB (s : StateB) : List ActB → StateB
  | [] => s
  | a :: as => runB (stepB s a) as

def initB : StateB := { out := .absent, stg1 := .absent, stg2 := .absent }

/-- Everything in a staging slot belongs to the builder that owns the slot. -/
def slotOwnedBy (b : Bldr) : Slot → Bool
  | .absent => true
  | .dir cs sealed =>
      cs.all (fun c => c == b) && (match sealed with | none => true | some x => x == b)

/-- No staging directory holds another builder's classes, and the published output is
sound. -/
def StateB.invariant (s : StateB) : Bool :=
  s.out.sound && slotOwnedBy .one s.stg1 && slotOwnedBy .two s.stg2

theorem sound_of_owned (b : Bldr) :
    ∀ v : Slot, slotOwnedBy b v = true → v.sound = true
  | .absent, _ => rfl
  | .dir _ none, _ => rfl
  | .dir cs (some x), h => by
      simp only [slotOwnedBy, Bool.and_eq_true, beq_iff_eq] at h
      simp only [Slot.sound]
      rw [h.2]
      exact h.1

theorem owned_addClass (b : Bldr) :
    ∀ v : Slot, slotOwnedBy b v = true → slotOwnedBy b (v.addClass b) = true
  | .absent, _ => rfl
  | .dir cs sealed, h => by
      simp only [slotOwnedBy, Bool.and_eq_true] at h
      simp only [Slot.addClass, slotOwnedBy, Bool.and_eq_true]
      exact ⟨by simp [h.1], h.2⟩

theorem owned_seal (b : Bldr) :
    ∀ v : Slot, slotOwnedBy b v = true → slotOwnedBy b (v.seal b) = true
  | .absent, _ => rfl
  | .dir cs sealed, h => by
      simp only [slotOwnedBy, Bool.and_eq_true] at h
      simp only [Slot.seal, slotOwnedBy, Bool.and_eq_true]
      exact ⟨h.1, by simp⟩

/-- Every step preserves the invariant, whichever builder takes it and whatever the other
builder has already done. -/
theorem stepB_preserves (s : StateB) (a : ActB) (h : s.invariant = true) :
    (stepB s a).invariant = true := by
  simp only [StateB.invariant, Bool.and_eq_true] at h
  obtain ⟨⟨hout, h1⟩, h2⟩ := h
  cases a with
  | reset b =>
      cases b <;>
        simp only [stepB, StateB.withStg, StateB.invariant, Bool.and_eq_true]
      · exact ⟨⟨hout, by simp [slotOwnedBy]⟩, h2⟩
      · exact ⟨⟨hout, h1⟩, by simp [slotOwnedBy]⟩
  | copy b =>
      cases b <;>
        simp only [stepB, StateB.withStg, StateB.stg, StateB.invariant, Bool.and_eq_true]
      · exact ⟨⟨hout, owned_addClass .one s.stg1 h1⟩, h2⟩
      · exact ⟨⟨hout, h1⟩, owned_addClass .two s.stg2 h2⟩
  | sealDir b =>
      cases b <;>
        simp only [stepB, StateB.withStg, StateB.stg, StateB.invariant, Bool.and_eq_true]
      · exact ⟨⟨hout, owned_seal .one s.stg1 h1⟩, h2⟩
      · exact ⟨⟨hout, h1⟩, owned_seal .two s.stg2 h2⟩
  | moveOutAside =>
      simp only [stepB, StateB.invariant, Bool.and_eq_true]
      exact ⟨⟨rfl, h1⟩, h2⟩
  | renameIn b =>
      cases b <;>
        simp only [stepB, StateB.withStg, StateB.stg, StateB.invariant, Bool.and_eq_true]
      · exact ⟨⟨sound_of_owned .one s.stg1 h1, by simp [slotOwnedBy]⟩, h2⟩
      · exact ⟨⟨sound_of_owned .two s.stg2 h2, h1⟩, by simp [slotOwnedBy]⟩

theorem runB_preserves : ∀ (s : StateB) (as : List ActB), s.invariant = true →
    (runB s as).invariant = true
  | _, [], h => h
  | s, a :: as, h => runB_preserves (stepB s a) as (stepB_preserves s a h)

/-- **The repaired protocol never publishes a mixture**, under any interleaving of the two
builders whatsoever. -/
theorem publishedOutputIsSound (as : List ActB) : (runB initB as).out.sound = true :=
  invariant_out (runB_preserves initB as rfl)
where
  invariant_out {s : StateB} (h : s.invariant = true) : s.out.sound = true := by
    simp only [StateB.invariant, Bool.and_eq_true] at h
    exact h.1.1

/-- And the interleaving that breaks protocol A is available to protocol B too — it is the
protocol, not the schedule, that differs. -/
theorem raceB_is_sound :
    (runB initB [.reset .one, .copy .one, .reset .two, .copy .two, .copy .one, .sealDir .two,
      .moveOutAside, .renameIn .two]).out = .dir [.two] (some .two) := rfl

#constructive raceA_publishes_a_mixture raceA_output_is_readable raceA_output_is_not_sound
#constructive sound_of_owned owned_addClass owned_seal stepB_preserves runB_preserves
#constructive publishedOutputIsSound raceB_is_sound

end Opentaint.Approximation
