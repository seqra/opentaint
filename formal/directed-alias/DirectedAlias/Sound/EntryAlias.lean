import DirectedAlias.Sound.Soundness

/-!
# Entry aliasing and the strong-update policy

Model of entry aliasing: the concrete frame `frC` binds two variables to ONE root object.
The analysis uses the frame `frA`, which binds them to two different roots (it has no
caller information). The examples show:
* No policy is sound under entry aliasing. Even the empty program is a counterexample.
* The weak policy (`entryUnique = false`) does not help for a read through the other root.
* The quotient frame (the caller tells which roots can be equal) is sound by `csoundE`.
* The swap example: the weak policy keeps the entry value, but only by chance.
-/

namespace DirectedAlias.Sound.EntryAlias

open DirectedAlias DirectedAlias.Sound

/-- Variable `x` (an argument). -/
abbrev vx : Var := 0
/-- Variable `y` (an argument). -/
abbrev vy : Var := 1
/-- Variable `z` (an argument). -/
abbrev vz : Var := 2
/-- Variable `t`. -/
abbrev vt : Var := 3
/-- Variable `u`. -/
abbrev vu : Var := 4
/-- Field `f`. -/
abbrev ff : Field := 0

/-- The concrete frame with entry aliasing: `x` and `y` hold the same object. -/
def frC : Frame := ⟨[(vx, 0), (vy, 0), (vz, 2)]⟩
/-- The analysis frame: `x` and `y` hold different roots (A1). -/
def frA : Frame := ⟨[(vx, 0), (vy, 1), (vz, 2)]⟩

/-- Under entry aliasing, the empty program aliases `x` and `y`, but no policy finds it. -/
theorem skip_unsound :
    CAlias frC .skip vx [] vy [] ∧ ∀ eu, mayProgE eu 2 frA .skip vx [] vy [] = false :=
  ⟨runAliasB_sound (cs := []) (by decide), fun eu => by cases eu <;> decide⟩

/-- The program `x.f = z`. -/
def pWrite : Prog := .stmt (.store vx ff vz)

/-- Under entry aliasing, `y.f` aliases `z` after `x.f = z`, but no policy finds it:
the read through `y` does not see the write through `x`. -/
theorem write_read_unsound :
    CAlias frC pWrite vy [.fld ff] vz [] ∧
      ∀ eu, mayProgE eu 2 frA pWrite vy [.fld ff] vz [] = false :=
  ⟨runAliasB_sound (cs := []) (by decide), fun eu => by cases eu <;> decide⟩

/-- With the quotient frame (caller information), both policies find the alias. -/
theorem write_read_quotient :
    ∀ eu, mayProgE eu 2 frC pWrite vy [.fld ff] vz [] = true :=
  fun eu => by cases eu <;> decide

/-- The swap of fields: `t = x.f; u = y.f; x.f = u; y.f = t`. -/
def pSwap : Prog :=
  .seq (.stmt (.load vt vx ff)) (.seq (.stmt (.load vu vy ff))
    (.seq (.stmt (.store vx ff vu)) (.stmt (.store vy ff vt))))

/-- Under entry aliasing, `swap(box, box)` leaves `x.f` equal to the entry value `t`. -/
theorem swap_alias : CAlias frC pSwap vx [.fld ff] vt [] :=
  runAliasB_sound (cs := []) (by decide)

/-- The strong policy with the A1 frame does not find the swap alias. -/
theorem swap_strong : mayProgE true 2 frA pSwap vx [.fld ff] vt [] = false := by decide

/-- The weak policy with the A1 frame finds the swap alias: it keeps the entry value. -/
theorem swap_weak : mayProgE false 2 frA pSwap vx [.fld ff] vt [] = true := by decide

/-- The strong policy with the quotient frame finds the swap alias. -/
theorem swap_quotient : mayProgE true 2 frC pSwap vx [.fld ff] vt [] = true := by decide

end DirectedAlias.Sound.EntryAlias
