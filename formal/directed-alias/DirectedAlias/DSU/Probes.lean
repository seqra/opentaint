import DirectedAlias.DSU.Examples
import DirectedAlias.DSU.HeapFree

/-!
# Validation of the DSU model against the measured Kotlin answers

Each theorem encodes one probe scenario of `R-probes.md` (sample `DirectedAliasSample.java`)
in the IR. It checks that the model gives the answer that the real analysis gave.
The end of the IR program is the probe point.
-/

namespace DirectedAlias.DSU.Probes

open DirectedAlias DirectedAlias.DSU DirectedAlias.DSU.Examples

/-- Field `value`. -/
abbrev fv : Field := 1
/-- Field `box`. -/
abbrev fb : Field := 0

/-- S7 `loopReassign`: `a = new; b = new; cur = a; while (*) cur = b`. -/
def s7 : Prog :=
  .seq (.stmt (.new 0 1)) <| .seq (.stmt (.new 1 2)) <| .seq (.stmt (.copy 2 0)) (.loop (.stmt (.copy 2 1)))

/-- S7: the model gives `a ~ b` and `a ~ cur`, as Kotlin (`alias(a) = [b, cur, new(a), new(b)]`). -/
theorem s7_matches :
    dsuMay kotlin ⟨[]⟩ s7 0 [] 1 [] = true ∧ dsuMay kotlin ⟨[]⟩ s7 0 [] 2 [] = true ∧
      mayProg 1 ⟨[]⟩ s7 0 [] 1 [] = false := by decide +kernel

/-- S8 `loadThroughJoinOfArgs`: `a = p | q; t = a.value; pv = p.value`. -/
def s8 : Prog :=
  .seq (.choice (.stmt (.copy 2 0)) (.stmt (.copy 2 1))) <|
  .seq (.stmt (.load 3 2 fv)) (.stmt (.load 4 0 fv))

/-- The frame of S8: `p`, `q` hold roots 0, 1. -/
def frS8 : Frame := ⟨[(0, 0), (1, 1)]⟩

/-- S8: the model gives `pv ~ q.value` and `pv ~ t`, as Kotlin. -/
theorem s8_matches :
    dsuMay kotlin frS8 s8 4 [] 1 [.fld fv] = true ∧ dsuMay kotlin frS8 s8 4 [] 3 [] = true ∧
      mayProg 1 frS8 s8 4 [] 1 [.fld fv] = false := by decide +kernel

/-- S9 `storeThroughJoinLoadThroughOtherAllocs`: `x, y, z = new; a = x | y; a.value = z; t = y.value`. -/
def s9 : Prog :=
  .seq (.stmt (.new 0 1)) <| .seq (.stmt (.new 1 2)) <| .seq (.stmt (.new 2 3)) <|
  .seq (.choice (.stmt (.copy 3 0)) (.stmt (.copy 3 1))) <|
  .seq (.stmt (.store 3 fv 2)) (.stmt (.load 4 1 fv))

/-- S9: the store is weak (two `Alloc`), so `t ~ z`, as Kotlin (`alias(t) = [new(z), z]`). -/
theorem s9_matches : dsuMay kotlin ⟨[]⟩ s9 4 [] 2 [] = true := by decide +kernel

/-- S11 `ThisWrites`: `this.value = v1; this.value = v2; t = this.value`. -/
def s11 : Prog :=
  .seq (.stmt (.store 0 fv 1)) <| .seq (.stmt (.store 0 fv 2)) (.stmt (.load 3 0 fv))

/-- The frame of S11: `this`, `v1`, `v2` hold roots 0, 1, 2. -/
def frS11 : Frame := ⟨[(0, 0), (1, 1), (2, 2)]⟩

/-- S11: strong in the constructor (`t` not `v1`), weak in the method (`t ~ v1`), as Kotlin. -/
theorem s11_matches :
    dsuMay ctor frS11 s11 3 [] 1 [] = false ∧ dsuMay ctor frS11 s11 3 [] 2 [] = true ∧
      dsuMay kotlin frS11 s11 3 [] 1 [] = true ∧ dsuMay kotlin frS11 s11 3 [] 2 [] = true := by
  decide +kernel

/-- The frame of S3.1 and S3.4: `h`, `pa`, `pw` hold roots 0, 1, 2. -/
def frS3 : Frame := ⟨[(0, 0), (1, 1), (2, 2)]⟩

/-- The loop body of S3.1: `seen = prev.value; cur = new; cur.value = pw; cur.value = pa; prev = cur`. -/
def s31body : Prog :=
  .seq (.stmt (.load 4 3 fv)) <| .seq (.stmt (.new 5 20)) <|
  .seq (.stmt (.store 5 fv 2)) <| .seq (.stmt (.store 5 fv 1)) (.stmt (.copy 3 5))

/-- S3.1 `loopSiteStrongUpdateAfterInvalidatedLoad`: `prev = h.box; touch(h); prev.value = pa;
loop { body }`, then the body up to the probe point. -/
def s31 : Prog :=
  .seq (.stmt (.load 3 0 fb)) <| .seq (.stmt (.call none 10 [0])) <|
  .seq (.stmt (.store 3 fv 1)) <| .seq (.loop s31body) <|
  .seq (.stmt (.load 4 3 fv)) <| .seq (.stmt (.new 5 20)) (.stmt (.store 5 fv 2))

/-- S3.1: the model loses `seen ~ prev.value` and keeps `seen ~ pa` and `prev.value ~ pw`, as Kotlin. -/
theorem s31_matches :
    dsuMay kotlin frS3 s31 4 [] 3 [.fld fv] = false ∧ dsuMay kotlin frS3 s31 4 [] 1 [] = true ∧
      dsuMay kotlin frS3 s31 3 [.fld fv] 2 [] = true := by decide +kernel

/-- S3.1: an execution (zero loop iterations) has `seen == prev.value`. -/
theorem s31_witness : CAlias frS3 s31 4 [] 3 [.fld fv] :=
  runAliasB_sound (cs := [.havoc [], .iter 0]) (by decide +kernel)

/-- S3.3 `CtorJoin`: `this.value = pa; seen = this.value; n = this | new; n.value = pw`. -/
def s33 : Prog :=
  .seq (.stmt (.store 0 fv 1)) <| .seq (.stmt (.load 3 0 fv)) <|
  .seq (.choice (.stmt (.copy 4 0)) (.stmt (.new 4 20))) (.stmt (.store 4 fv 2))

/-- S3.3: in a constructor the model loses `seen ~ this.value`, as Kotlin (`alias(seen) = [arg:pa]`). -/
theorem s33_matches :
    dsuMay ctor frS3 s33 3 [] 0 [.fld fv] = false ∧ dsuMay ctor frS3 s33 3 [] 1 [] = true := by
  decide +kernel

/-- S3.3: the execution with `n = new` keeps `seen == this.value`. -/
theorem s33_witness : CAlias frS3 s33 3 [] 0 [.fld fv] :=
  runAliasB_sound (cs := [.right]) (by decide +kernel)

/-- S3.4 `joinOfInvalidatedLoadAndAlloc`: `p = h.box; touch(h); p.value = pa; seen = p.value;
n = p | new; n.value = pw`. -/
def s34 : Prog :=
  .seq (.stmt (.load 3 0 fb)) <| .seq (.stmt (.call none 10 [0])) <|
  .seq (.stmt (.store 3 fv 1)) <| .seq (.stmt (.load 4 3 fv)) <|
  .seq (.choice (.stmt (.copy 5 3)) (.stmt (.new 5 20))) (.stmt (.store 5 fv 2))

/-- S3.4: the model loses `seen ~ p.value` and gives `p.value ~ pw`, as Kotlin. -/
theorem s34_matches :
    dsuMay kotlin frS3 s34 4 [] 3 [.fld fv] = false ∧ dsuMay kotlin frS3 s34 4 [] 1 [] = true ∧
      dsuMay kotlin frS3 s34 3 [.fld fv] 2 [] = true := by decide +kernel

/-- S3.4: the execution with `n = new` keeps `seen == p.value`. -/
theorem s34_witness : CAlias frS3 s34 4 [] 3 [.fld fv] :=
  runAliasB_sound (cs := [.havoc [], .right]) (by decide +kernel)

/-- S4 `loadThenUnrelatedCallCopiedArg`: `x = px; w = x.value; touch(other)`. -/
def s4copied : Prog := .seq (.stmt (.load 2 0 fv)) (.stmt (.call none 10 [1]))

/-- S4: the copied argument is outer, so the model removes `x.value`, as Kotlin (`alias(w) = []`). -/
theorem s4copied_matches : dsuMay kotlin ⟨[(0, 0), (1, 1)]⟩ s4copied 2 [] 0 [.fld fv] = false := by
  decide +kernel

/-! ## Use of the fragment theorems -/

/-- The soundness theorem gives the DSU alias `a ~ x` of the task example from one execution. -/
theorem sound_on_pJoin : dsuMay kotlin Examples.fr Examples.pJoin Examples.va [] Examples.vx [] = true :=
  dsu_sound_heapFree (px := []) (py := []) (by decide) (by decide +kernel) Examples.join_a_x_witness

/-- The dominance theorem gives the DSU alias `a ~ y` of the task example from the concept alias. -/
theorem dominates_on_pJoin :
    dsuMay kotlin Examples.fr Examples.pJoin Examples.va [] Examples.vy [] = true :=
  dsu_dominates_heapFree 2 (by decide) (by decide +kernel) (aOk_loopFree _ _ _ rfl) Examples.join_a_y

/-- The dominance theorem applies to the loop of S7: the concept loop converges. -/
theorem dominates_on_s7 : dsuMay kotlin ⟨[]⟩ s7 0 [] 2 [] = true :=
  dsu_dominates_heapFree 1 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end DirectedAlias.DSU.Probes
