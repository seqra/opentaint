/-- Public and scoped rows are merged into disjoint partitions. Index
    construction is a read of the merged rows and has no inter-phase reader. -/
structure RecordPartitions (Public Scoped : Type) where
  publicRows : Public
  scopedRows : Scoped

def replacePublic {Public Scoped : Type} (merge : Public → Public)
    (rows : RecordPartitions Public Scoped) : RecordPartitions Public Scoped :=
  { rows with publicRows := merge rows.publicRows }

def replaceScoped {Public Scoped : Type} (merge : Scoped → Scoped)
    (rows : RecordPartitions Public Scoped) : RecordPartitions Public Scoped :=
  { rows with scopedRows := merge rows.scopedRows }

def rebuildTwice {Public Scoped Index : Type}
    (mp : Public → Public) (ms : Scoped → Scoped)
    (index : RecordPartitions Public Scoped → Index)
    (rows : RecordPartitions Public Scoped) : Index × Index :=
  let afterPublic := replacePublic mp rows
  (index afterPublic, index (replaceScoped ms afterPublic))

def rebuildOnce {Public Scoped Index : Type}
    (mp : Public → Public) (ms : Scoped → Scoped)
    (index : RecordPartitions Public Scoped → Index)
    (rows : RecordPartitions Public Scoped) : Index :=
  index ⟨mp rows.publicRows, ms rows.scopedRows⟩

theorem oneRebuildSameFinalIndex {Public Scoped Index : Type}
    (mp : Public → Public) (ms : Scoped → Scoped)
    (index : RecordPartitions Public Scoped → Index)
    (rows : RecordPartitions Public Scoped) :
    rebuildOnce mp ms index rows = (rebuildTwice mp ms index rows).2 := rfl

/-- The omitted intermediate pass contains today's public rows and
    yesterday's scoped rows. Today's scoped changes cannot fund the check. -/
theorem omittedRebuildCount {Public Scoped : Type}
    (mp : Public → Public) (ms : Scoped → Scoped)
    (pc : Public → Nat) (sc : Scoped → Nat)
    (rows : RecordPartitions Public Scoped) :
    (rebuildTwice mp ms (fun x => pc x.publicRows + sc x.scopedRows) rows).1 =
      pc (mp rows.publicRows) + sc rows.scopedRows := rfl

/-- One resource class within one scan. Capping the balance discards
    credit and cannot make a reservation possible earlier. -/
structure ProofWorkBalance where
  saved : Nat
  reserved : Nat
  available : Nat

def ProofWorkBalance.valid (b : ProofWorkBalance) : Prop :=
  b.reserved + b.available ≤ b.saved

def ProofWorkBalance.credit (b : ProofWorkBalance) (limit removed : Nat) :
    ProofWorkBalance :=
  ⟨b.saved + removed, b.reserved, min limit (b.available + removed)⟩

def ProofWorkBalance.reserve (b : ProofWorkBalance) (bound : Nat) :
    Option ProofWorkBalance :=
  if bound ≤ b.available then
    some ⟨b.saved, b.reserved + bound, b.available - bound⟩
  else none

theorem ProofWorkBalance.credit_valid (b : ProofWorkBalance) (ok : b.valid)
    (limit removed : Nat) : (b.credit limit removed).valid := by
  unfold ProofWorkBalance.valid ProofWorkBalance.credit at *
  change b.reserved + min limit (b.available + removed) ≤ b.saved + removed
  have bounded := Nat.min_le_right limit (b.available + removed)
  omega

theorem ProofWorkBalance.reserve_valid (b after : ProofWorkBalance) (ok : b.valid)
    (bound : Nat) (funded : b.reserve bound = some after) : after.valid := by
  unfold ProofWorkBalance.reserve at funded
  split at funded
  · rename_i fits
    cases funded
    unfold ProofWorkBalance.valid at *
    change b.reserved + bound + (b.available - bound) ≤ b.saved
    omega
  · contradiction

theorem ProofWorkBalance.no_future_credit (b after : ProofWorkBalance)
    (ok : b.valid) (bound : Nat) (funded : b.reserve bound = some after) :
    after.reserved ≤ b.saved := by
  have h := reserve_valid b after ok bound funded
  unfold ProofWorkBalance.reserve at funded
  split at funded
  · cases funded
    exact Nat.le_trans (Nat.le_add_right _ _) h
  · contradiction

/-- Keep the ordered reference view of the current records while they
    are already owned by the record indexes. Only the generation goes
    into a temporal proof snapshot. A new order or record reference
    increments it and rejects the proof. -/
structure SealedOrder (Key : Type) where
  rows : List Key
  generation : Nat

def SealedOrder.rebuild {Key : Type} [DecidableEq Key]
    (s : SealedOrder Key) (actual : List Key) : SealedOrder Key :=
  if s.rows = actual then s else ⟨actual, s.generation + 1⟩

theorem SealedOrder.generation_mono {Key : Type} [DecidableEq Key]
    (s : SealedOrder Key) (actual : List Key) :
    s.generation ≤ (s.rebuild actual).generation := by
  unfold SealedOrder.rebuild
  split <;> simp

theorem SealedOrder.equal_generation_keeps_order {Key : Type} [DecidableEq Key]
    (s : SealedOrder Key) (actual : List Key)
    (stable : (s.rebuild actual).generation = s.generation) :
    actual = s.rows := by
  unfold SealedOrder.rebuild at stable
  split at stable
  · rename_i same
    exact same.symm
  · exact False.elim (Nat.ne_of_gt (Nat.lt_succ_self s.generation) stable)

theorem SealedOrder.rebuild_rows {Key : Type} [DecidableEq Key]
    (s : SealedOrder Key) (actual : List Key) :
    (s.rebuild actual).rows = actual := by
  unfold SealedOrder.rebuild
  split
  · assumption
  · rfl

theorem SealedOrder.equal_generation_two_seals {Key : Type} [DecidableEq Key]
    (s : SealedOrder Key) (backward forward : List Key)
    (stable : ((s.rebuild backward).rebuild forward).generation = s.generation) :
    backward = s.rows ∧ forward = s.rows := by
  have step1 := s.generation_mono backward
  have step2 := (s.rebuild backward).generation_mono forward
  have step1Rev : (s.rebuild backward).generation ≤ s.generation :=
    stable ▸ step2
  have same1 : (s.rebuild backward).generation = s.generation :=
    Nat.le_antisymm step1Rev step1
  have same2 : ((s.rebuild backward).rebuild forward).generation =
      (s.rebuild backward).generation := stable.trans same1.symm
  have keep1 := s.equal_generation_keeps_order backward same1
  have keep2 := (s.rebuild backward).equal_generation_keeps_order forward same2
  exact ⟨keep1, keep2.trans ((s.rebuild_rows backward).trans keep1)⟩

example : (SealedOrder.rebuild ⟨[1, 2], 9⟩ [2, 1]).generation = 10 := rfl

/-- The target builder inserts old ordered rows first. Thus a final
    sequence of unchanged size proves exact equality when the old
    sequence is a prefix. This includes the index insertion order. -/
theorem orderedExtensionSameSize {Key : Type} (before additions : List Key)
    (sameSize : (before ++ additions).length = before.length) :
    before ++ additions = before := by
  rw [List.length_append] at sameSize
  have sum : before.length + additions.length = before.length + 0 := sameSize
  have empty := List.length_eq_zero_iff.mp (Nat.add_left_cancel sum)
  rw [empty, List.append_nil]
