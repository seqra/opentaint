/-
  A named field cleaner lowers to read / clean a fresh temporary / strong writeback.
  The concrete contract projects away the temporary at both ends. This is a local
  alias-free lowering proof, not a theorem about whole-program iteration.
-/
import ApSpec.AbsDefs
import ApSpec.HandoffCases

namespace ApSpec.CleanerLowering
open ApSpec ApSpec.Reverse ApSpec.Handoff

theorem beq_false {a b : Nat} : Nat.beq a b = false ↔ a ≠ b := by
  constructor
  · intro h he
    subst b
    rw [Nat.beq_refl] at h
    exact Bool.noConfusion h
  · intro h
    cases he : Nat.beq a b with
    | false => rfl
    | true => exact False.elim (h (CoreAux.beq_iff.mp he))

attribute [local simp] beq_false

/-- Reading must touch its source for `transfer` to visit the read micro edge. -/
def readEdge (b u : Base) (g : Acc) : MicroEdge :=
  (⟨b, [g], .star Excl.empty, .star⟩, ⟨u, [], .star Excl.empty, .star⟩)
def writeEdge (b u : Base) (g : Acc) : MicroEdge :=
  (⟨u, [], .star Excl.empty, .star⟩, ⟨b, [g], .star Excl.empty, .star⟩)
def keepEdge (b : Base) (g : Acc) : MicroEdge :=
  (⟨b, [], .star (.set [g]), .star⟩, ⟨b, [], .star (.set [g]), .star⟩)
def readStmt (b u : Base) (g : Acc) : Stmt := ⟨[b, u], [idEdge b, readEdge b u g]⟩
def writeStmt (b u : Base) (g : Acc) : Stmt :=
  ⟨[b, u], [keepEdge b g, idEdge u, writeEdge b u g]⟩
/-- The temporary cleaner keeps the selected reach and mark policy. -/
def tempCleanerWith (u : Base) (reach : CleanReach) (mark : Option Mark) : Cleaner :=
  ⟨u, [], reach, mark⟩
/-- The local named-field cleaner with any reach and one or every mark. -/
def fieldCleanerWith (b : Base) (g : Acc) (reach : CleanReach) (mark : Option Mark) : Cleaner :=
  ⟨b, [g], reach, mark⟩
def tempCleaner (u : Base) (t : Mark) : Cleaner := tempCleanerWith u .atAndBelow (some t)
def fieldCleaner (b : Base) (g : Acc) (t : Mark) : Cleaner :=
  fieldCleanerWith b g .atAndBelow (some t)

/-- A read moves exactly the selected subtree to the fresh temporary. -/
theorem read_pair {b u : Base} {g : Acc} {l a : Loc} :
    den (readEdge b u g).1 (readEdge b u g).2 l a ↔
    l.base = b ∧ ∃ σ, l.path = g :: σ ∧ a = ⟨u, σ, l.mark⟩ := by
  constructor
  · rintro ⟨hb, hu, _, hm, _, σ, τ, hp, hq, _, hτσ, _⟩
    refine ⟨hb, σ, hp, ?_⟩
    cases a
    simp only [Loc.mk.injEq]
    exact ⟨hu, hq.trans hτσ, hm⟩
  · rintro ⟨hb, σ, hp, rfl⟩
    exact ⟨hb, rfl, trivial, rfl, trivial, σ, σ, hp, rfl,
      empty_admits σ, rfl, empty_admits σ⟩

/-- A write moves the temporary subtree back without changing its mark. -/
theorem write_pair {b u : Base} {g : Acc} {a l : Loc} :
    den (writeEdge b u g).1 (writeEdge b u g).2 a l ↔
    a.base = u ∧ l = ⟨b, g :: a.path, a.mark⟩ := by
  constructor
  · rintro ⟨hu, hb, _, hm, _, σ, τ, hp, hq, _, hτσ, _⟩
    have hp' : a.path = σ := hp
    cases l
    simp only [Loc.mk.injEq]
    exact ⟨hu, hb, by simpa [writeEdge, ← hp', hτσ] using hq, hm⟩
  · rintro ⟨hu, rfl⟩
    exact ⟨hu, rfl, trivial, rfl, trivial, a.path, a.path, rfl, rfl,
      empty_admits a.path, rfl, empty_admits a.path⟩

/-- The strong-write keep edge is the identity outside the written subtree. -/
theorem keep_pair {b : Base} {g : Acc} {l a : Loc} :
    den (keepEdge b g).1 (keepEdge b g).2 l a ↔
    l.base = b ∧ a = l ∧ (Excl.set [g]).admits l.path = true := by
  constructor
  · rintro ⟨hb, ha, _, hm, _, σ, τ, hp, hq, hs, hτσ, _⟩
    have hp' : l.path = σ := hp
    refine ⟨hb, ?_, ?_⟩
    · cases l
      cases a
      simp only [Loc.mk.injEq]
      exact ⟨ha.trans hb.symm, hq.trans (hτσ.trans hp'.symm), hm⟩
    · simpa [keepEdge, tailI, hp'] using hs
  · rintro ⟨hb, he, hs⟩
    subst a
    exact ⟨hb, hb, trivial, rfl, trivial, l.path, l.path, rfl, rfl, hs, rfl, hs⟩

/-- Every old location survives the read itself; it may additionally flow to tmp. -/
theorem read_old {b u : Base} {g : Acc} {l a : Loc} (hu : l.base ≠ u) :
    (readStmt b u g).step l a ↔
    a = l ∨ (l.base = b ∧ ∃ σ, l.path = g :: σ ∧ a = ⟨u, σ, l.mark⟩) := by
  constructor
  · rintro (⟨_, ha⟩ | ⟨e, he, hd⟩)
    · exact .inl ha
    · simp [readStmt] at he
      rcases he with rfl | rfl
      · exact .inl (den_idEdge.mp hd).2
      · exact .inr (read_pair.mp hd)
  · rintro (ha | hr)
    · subst a
      by_cases hb : l.base = b
      · exact .inr ⟨idEdge b, by simp [readStmt], den_idEdge.mpr ⟨hb, rfl⟩⟩
      · exact .inl ⟨by simp [readStmt, memB, hb, hu], rfl⟩
    · exact .inr ⟨readEdge b u g, by simp [readStmt], read_pair.mpr hr⟩

/-- After projecting away tmp, a strong write either preserves an old location
    outside the field or returns the corresponding temporary location. -/
theorem write_old {b u : Base} {g : Acc} {a l : Loc} (hu : l.base ≠ u) :
    (writeStmt b u g).step a l ↔
    (l = a ∧ a.base ≠ u ∧ (a.base ≠ b ∨ (Excl.set [g]).admits a.path = true)) ∨
    (a.base = u ∧ l = ⟨b, g :: a.path, a.mark⟩) := by
  constructor
  · rintro (⟨hm, rfl⟩ | ⟨e, he, hd⟩)
    · refine .inl ⟨rfl, hu, .inl ?_⟩
      intro hb
      simp [writeStmt, memB, hb] at hm
    · simp [writeStmt] at he
      rcases he with rfl | rfl | rfl
      · obtain ⟨hb, hl, hs⟩ := keep_pair.mp hd
        exact .inl ⟨hl, by simpa [hl] using hu, .inr hs⟩
      · obtain ⟨hb, hl⟩ := den_idEdge.mp hd
        exact False.elim (hu (hl ▸ hb))
      · exact .inr (write_pair.mp hd)
  · rintro (⟨hl, ha, hb | hs⟩ | hw)
    · subst l
      exact .inl ⟨by simp [writeStmt, memB, hb, ha], rfl⟩
    · subst l
      by_cases hb : a.base = b
      · exact .inr ⟨keepEdge b g, by simp [writeStmt], keep_pair.mpr ⟨hb, rfl, hs⟩⟩
      · exact .inl ⟨by simp [writeStmt, memB, hb, ha], rfl⟩
    · exact .inr ⟨writeEdge b u g, by simp [writeStmt], write_pair.mpr hw⟩

/-- The three actual lowered operations, with tmp projected away at the ends. -/
def LoweredWith (b u : Base) (g : Acc) (reach : CleanReach) (mark : Option Mark) (l l' : Loc) : Prop :=
  ∃ a, (readStmt b u g).step l a ∧ (tempCleanerWith u reach mark).cleansB a = false ∧
    (writeStmt b u g).step a l'

/-- Semantic equivalence to a field cleaner on old locations. Freshness and
    temporary projection are explicit; every reach and mark policy is covered. -/
theorem loweredWith_iff {b u : Base} {g : Acc} {reach : CleanReach} {mark : Option Mark} {l l' : Loc}
    (_hbu : b ≠ u) (hu : l.base ≠ u) (hu' : l'.base ≠ u) :
    LoweredWith b u g reach mark l l' ↔ l' = l ∧ (fieldCleanerWith b g reach mark).cleansB l = false := by
  constructor
  · rintro ⟨a, hr, hc, hw⟩
    rcases (read_old hu).mp hr with ha | ⟨hb, σ, hp, ha⟩
    · subst a
      rcases (write_old hu').mp hw with ⟨hl, _, hb | hs⟩ | ⟨ha, _⟩
      · exact ⟨hl, by simp [fieldCleanerWith, Cleaner.cleansB, hb]⟩
      · refine ⟨hl, ?_⟩
        cases hp : l.path with
        | nil => simp [fieldCleanerWith, Cleaner.cleansB, hp, dropPrefix]
        | cons k ks =>
          have hkg : k ≠ g := by simpa [hp, Excl.admits, memB] using hs
          simp [fieldCleanerWith, Cleaner.cleansB, hp, dropPrefix, Ne.symm hkg]
      · exact False.elim (hu ha)
    · subst a
      rcases (write_old hu').mp hw with ⟨_, ha, _⟩ | ⟨_, hl⟩
      · exact False.elim (ha rfl)
      · have he : l' = l := by
          cases l
          simp only at hb hp
          simpa [hb, hp] using hl
        refine ⟨he, ?_⟩
        simpa [fieldCleanerWith, tempCleanerWith, Cleaner.cleansB, Cleaner.markB, CleanReach.inB,
          hb, hp, dropPrefix] using hc
  · rintro ⟨he, hc⟩
    subst l'
    by_cases hb : l.base = b
    · cases hp : l.path with
      | nil =>
        refine ⟨l, (read_old hu).mpr (.inl rfl), ?_, (write_old hu).mpr (.inl ⟨rfl, hu, .inr (by rw [hp]; rfl)⟩)⟩
        simp [tempCleanerWith, Cleaner.cleansB, hu]
      | cons k ks =>
        by_cases hkg : k = g
        · subst k
          refine ⟨⟨u, ks, l.mark⟩, (read_old hu).mpr (.inr ⟨hb, ks, hp, rfl⟩), ?_, ?_⟩
          · simpa [fieldCleanerWith, tempCleanerWith, Cleaner.cleansB, Cleaner.markB, CleanReach.inB,
              hb, hp, dropPrefix] using hc
          · apply (write_old hu).mpr
            refine .inr ⟨rfl, ?_⟩
            cases l
            simp only [Loc.mk.injEq, and_true]
            exact ⟨hb, hp⟩
        · refine ⟨l, (read_old hu).mpr (.inl rfl), ?_, ?_⟩
          · simp [tempCleanerWith, Cleaner.cleansB, hu]
          · exact (write_old hu).mpr (.inl ⟨rfl, hu, .inr (by
              simp [hp, Excl.admits, memB, hkg])⟩)
    · refine ⟨l, (read_old hu).mpr (.inl rfl), ?_, (write_old hu).mpr (.inl ⟨rfl, hu, .inl hb⟩)⟩
      simp [tempCleanerWith, Cleaner.cleansB, hu]

/-- The original one-mark at-and-below relation. -/
def Lowered (b u : Base) (g : Acc) (t : Mark) (l l' : Loc) : Prop :=
  LoweredWith b u g .atAndBelow (some t) l l'

/-- Compatibility theorem for the original cleaner API. -/
theorem lowered_iff {b u : Base} {g : Acc} {t : Mark} {l l' : Loc}
    (hbu : b ≠ u) (hu : l.base ≠ u) (hu' : l'.base ≠ u) :
    Lowered b u g t l l' ↔ l' = l ∧ (fieldCleaner b g t).cleansB l = false :=
  loweredWith_iff hbu hu hu'

/-- The intermediate concrete location is computed from the input location. -/
def lowerMiddle (b u : Base) (g : Acc) (l : Loc) : Loc :=
  if l.base = b then
    match l.path with
    | [] => l
    | k :: ks => if k = g then ⟨u, ks, l.mark⟩ else l
  else l

/-- The local lowering witness is data, with certificates for all three operations. -/
def lowerWitnessWith (b u : Base) (g : Acc) (reach : CleanReach) (mark : Option Mark) (l : Loc)
    (hu : l.base ≠ u) (hc : (fieldCleanerWith b g reach mark).cleansB l = false) :
    {a : Loc // (readStmt b u g).step l a ∧ (tempCleanerWith u reach mark).cleansB a = false ∧
      (writeStmt b u g).step a l} :=
  ⟨lowerMiddle b u g l, by
    by_cases hb : l.base = b
    · cases hp : l.path with
      | nil =>
        simp only [lowerMiddle, hb, hp, ↓reduceIte]
        refine ⟨(read_old hu).mpr (.inl rfl), ?_,
          (write_old hu).mpr (.inl ⟨rfl, hu, .inr (by rw [hp]; rfl)⟩)⟩
        simp [tempCleanerWith, Cleaner.cleansB, hu]
      | cons k ks =>
        by_cases hkg : k = g
        · subst k
          simp only [lowerMiddle, hb, hp, ↓reduceIte]
          refine ⟨(read_old hu).mpr (.inr ⟨hb, ks, hp, rfl⟩), ?_, ?_⟩
          · simpa [fieldCleanerWith, tempCleanerWith, Cleaner.cleansB, Cleaner.markB, CleanReach.inB,
              hb, hp, dropPrefix] using hc
          · apply (write_old hu).mpr
            refine .inr ⟨rfl, ?_⟩
            cases l
            simp only [Loc.mk.injEq, and_true]
            exact ⟨hb, hp⟩
        · simp only [lowerMiddle, hb, hp, if_pos, if_neg hkg]
          refine ⟨(read_old hu).mpr (.inl rfl), ?_, ?_⟩
          · simp [tempCleanerWith, Cleaner.cleansB, hu]
          · exact (write_old hu).mpr (.inl ⟨rfl, hu, .inr (by
              simp [hp, Excl.admits, memB, hkg])⟩)
    · simp only [lowerMiddle, if_neg hb]
      refine ⟨(read_old hu).mpr (.inl rfl), ?_, (write_old hu).mpr (.inl ⟨rfl, hu, .inl hb⟩)⟩
      simp [tempCleanerWith, Cleaner.cleansB, hu]⟩

/-- The certificate returns the computed location for every policy. -/
theorem lowerWitnessWith_val (b u : Base) (g : Acc) (reach : CleanReach)
    (mark : Option Mark) (l : Loc) (hu : l.base ≠ u)
    (hc : (fieldCleanerWith b g reach mark).cleansB l = false) :
    (lowerWitnessWith b u g reach mark l hu hc).val = lowerMiddle b u g l := rfl

/-- Compatibility witness for one mark at and below the field. -/
def lowerWitness (b u : Base) (g : Acc) (t : Mark) (l : Loc)
    (hu : l.base ≠ u) (hc : (fieldCleaner b g t).cleansB l = false) :
    {a : Loc // (readStmt b u g).step l a ∧ (tempCleaner u t).cleansB a = false ∧
      (writeStmt b u g).step a l} :=
  lowerWitnessWith b u g .atAndBelow (some t) l hu hc

/-- A coarse FLOW fact reaching the reversed strong write. -/
def coarse (b : Base) : AFact := ⟨⟨b, [], .star Excl.empty, .star⟩, false⟩
/-- The reversed keep row doubles the syntactic exclusion; its meaning is {g}. -/
def backwardKeep (b : Base) (g : Acc) : AFact :=
  ⟨⟨b, [], .star (.set [g, g]), .star⟩, false⟩

theorem apply_backward_keep (b : Base) (g : Acc) :
    applyEdge (coarse b) (revEdge (keepEdge b g).1 (keepEdge b g).2).1
      (revEdge (keepEdge b g).1 (keepEdge b g).2).2 = ⟨[backwardKeep b g], []⟩ := by
  simp [coarse, backwardKeep, keepEdge, revEdge, revKinds, applyEdge, relate, dropPrefix,
    belowCase, admitsTailB, Excl.admits, tailExcl, Excl.empty, Excl.union,
    markGate, markComp, AFact.norm]

theorem apply_backward_read_keep (b : Base) (g : Acc) :
    applyEdge (backwardKeep b g) (revEdge (idEdge b).1 (idEdge b).2).1
      (revEdge (idEdge b).1 (idEdge b).2).2 = ⟨[backwardKeep b g], []⟩ := by
  simp [backwardKeep, idEdge, revEdge, revKinds, applyEdge, relate, dropPrefix,
    belowCase, admitsTailB, Excl.admits, tailExcl, Excl.empty, Excl.union,
    markGate, markComp, AFact.norm]

/-- Actual backward transfer contains the keep branch, for every field limit. -/
theorem backward_write_keep (b u : Base) (g : Acc) (counted : Acc → Bool) (L : Nat) :
    backwardKeep b g ∈ (transfer counted L (Stmt.rev (writeStmt b u g)) (coarse b)).facts := by
  have he : revEdge (keepEdge b g).1 (keepEdge b g).2 ∈ (Stmt.rev (writeStmt b u g)).edges := by
    apply List.mem_append.mpr
    apply Or.inl
    apply List.mem_map.mpr
    exact ⟨keepEdge b g, by simp [writeStmt], rfl⟩
  have hx : backwardKeep b g ∈ (applyAll (coarse b) (Stmt.rev (writeStmt b u g)).edges).facts :=
    CoreAux.mem_applyAll_facts he (by rw [apply_backward_keep]; exact List.mem_singleton.mpr rfl)
  have ht : memB (coarse b).fact.base (Stmt.rev (writeStmt b u g)).touched = true := by
    simp [coarse, Stmt.rev, writeStmt, memB]
  unfold transfer
  rw [ht, if_pos rfl]
  apply List.mem_map.mpr
  exact ⟨backwardKeep b g, hx, by simp [limitF, backwardKeep, cutPath]⟩

/-- Cleaning tmp is spatially disjoint from the old-base keep branch. -/
theorem backward_keep_clean_with {b u : Base} {g : Acc}
    {reach : CleanReach} {mark : Option Mark} (hbu : b ≠ u) :
    cleanPos (tempCleanerWith u reach mark) (backwardKeep b g).fact = .disjoint ∧
    cleanRes (tempCleanerWith u reach mark) (backwardKeep b g) = ⟨[backwardKeep b g], []⟩ := by
  have hp : cleanPos (tempCleanerWith u reach mark) (backwardKeep b g).fact = .disjoint := by
    simp [cleanPos, tempCleanerWith, backwardKeep, hbu]
  exact ⟨hp, by simp [cleanRes, hp]⟩

theorem backward_keep_clean {b u : Base} {g : Acc} {t : Mark} (hbu : b ≠ u) :
    cleanPos (tempCleaner u t) (backwardKeep b g).fact = .disjoint ∧
    cleanRes (tempCleaner u t) (backwardKeep b g) = ⟨[backwardKeep b g], []⟩ :=
  backward_keep_clean_with hbu

/-- Reversing the read preserves the same old-base keep branch. -/
theorem backward_read_keep (b u : Base) (g : Acc) (counted : Acc → Bool) (L : Nat) :
    backwardKeep b g ∈ (transfer counted L (Stmt.rev (readStmt b u g)) (backwardKeep b g)).facts := by
  have he : revEdge (idEdge b).1 (idEdge b).2 ∈ (Stmt.rev (readStmt b u g)).edges := by
    apply List.mem_append.mpr
    apply Or.inl
    apply List.mem_map.mpr
    exact ⟨idEdge b, by simp [readStmt], rfl⟩
  have hx : backwardKeep b g ∈ (applyAll (backwardKeep b g) (Stmt.rev (readStmt b u g)).edges).facts :=
    CoreAux.mem_applyAll_facts he (by rw [apply_backward_read_keep]; exact List.mem_singleton.mpr rfl)
  have ht : memB (backwardKeep b g).fact.base (Stmt.rev (readStmt b u g)).touched = true := by
    simp [backwardKeep, Stmt.rev, readStmt, memB]
  unfold transfer
  rw [ht, if_pos rfl]
  apply List.mem_map.mpr
  exact ⟨backwardKeep b g, hx, by simp [limitF, backwardKeep, cutPath]⟩

/-- The keep branch preserves every mark on every continuation outside g. -/
theorem backward_keep_all_marks (b : Base) (g : Acc) (σ : List Acc) (t : Mark)
    (hs : (Excl.set [g]).admits σ = true) :
    den (coarse b).fact (backwardKeep b g).fact ⟨b, σ, t⟩ ⟨b, σ, t⟩ := by
  have hs' : (Excl.set [g, g]).admits σ = true := by
    cases σ with
    | nil => rfl
    | cons k ks => simpa [Excl.admits, memB] using hs
  exact ⟨rfl, rfl, trivial, rfl, trivial, σ, σ, rfl, rfl, empty_admits σ, rfl, hs'⟩

/-- The branch remains a normal crossable record; it contains no mark deletion. -/
theorem backward_keep_crossable (b : Base) (g : Acc) :
    CrossB (coarse b).fact (backwardKeep b g) := by
  simp [CrossB, Cross, CrossK, coarse, backwardKeep, revRec, revEdge, revKinds, MarkRev,
    Excl.empty, Excl.union]

/-- An executable certificate for the actual AP backward keep trajectory. -/
def backwardKeepWitnessWith (b u : Base) (g : Acc) (reach : CleanReach)
    (mark : Option Mark) (counted : Acc → Bool) (L : Nat)
    (hbu : b ≠ u) :
    {f : AFact // f ∈ (transfer counted L (Stmt.rev (writeStmt b u g)) (coarse b)).facts ∧
      cleanRes (tempCleanerWith u reach mark) f = ⟨[f], []⟩ ∧
      f ∈ (transfer counted L (Stmt.rev (readStmt b u g)) f).facts ∧ f.fact.mark = .star} :=
  ⟨backwardKeep b g, backward_write_keep b u g counted L, (backward_keep_clean_with hbu).2,
    backward_read_keep b u g counted L, rfl⟩

/-- The executable AP certificate returns the same keep row for every policy. -/
theorem backwardKeepWitnessWith_val (b u : Base) (g : Acc) (reach : CleanReach)
    (mark : Option Mark) (counted : Acc → Bool) (L : Nat) (hbu : b ≠ u) :
    (backwardKeepWitnessWith b u g reach mark counted L hbu).val = backwardKeep b g := rfl

/-- Compatibility certificate for the original one-mark cleaner. -/
def backwardKeepWitness (b u : Base) (g : Acc) (t : Mark) (counted : Acc → Bool) (L : Nat)
    (hbu : b ≠ u) :
    {f : AFact // f ∈ (transfer counted L (Stmt.rev (writeStmt b u g)) (coarse b)).facts ∧
      cleanRes (tempCleaner u t) f = ⟨[f], []⟩ ∧
      f ∈ (transfer counted L (Stmt.rev (readStmt b u g)) f).facts ∧ f.fact.mark = .star} :=
  backwardKeepWitnessWith b u g .atAndBelow (some t) counted L hbu

theorem outside_field_not_cleaned_with {b : Base} {g : Acc} {m : Mark}
    {reach : CleanReach} {mark : Option Mark} {σ : List Acc}
    (hs : (Excl.set [g]).admits σ = true) :
    (fieldCleanerWith b g reach mark).cleansB ⟨b, σ, m⟩ = false := by
  cases σ with
  | nil => simp [fieldCleanerWith, Cleaner.cleansB, dropPrefix]
  | cons k ks =>
    have hkg : k ≠ g := by simpa [Excl.admits, memB] using hs
    simp [fieldCleanerWith, Cleaner.cleansB, dropPrefix, Ne.symm hkg]

/-- The reversed keep record denotes only real lowered flows, after projection.
    Its path exclusion, rather than a mark exclusion, excludes the cleaned field. -/
theorem backward_keep_record_sound_with {b u : Base} {g : Acc}
    {reach : CleanReach} {mark : Option Mark} {l0 l : Loc}
    (hbu : b ≠ u)
    (hd : den (revRec ((coarse b).fact, backwardKeep b g)).1
      (revRec ((coarse b).fact, backwardKeep b g)).2.fact l0 l) :
    LoweredWith b u g reach mark l0 l := by
  change den (coarse b).fact (backwardKeep b g).fact l0 l at hd
  rcases hd with ⟨hb0, hb, _, hm, _, σ, τ, hp0, hp, _, hτσ, hadm⟩
  change l0.base = b at hb0
  change l.base = b at hb
  change l.mark = l0.mark at hm
  have hp0' : l0.path = σ := hp0
  have hl : l = l0 := by
    cases l0
    cases l
    simp only [Loc.mk.injEq]
    exact ⟨hb.trans hb0.symm, hp.trans (hτσ.trans hp0'.symm), hm⟩
  have hs : (Excl.set [g]).admits l0.path = true := by
    change (Excl.set [g, g]).admits σ = true at hadm
    cases σ with
    | nil => rw [hp0']; rfl
    | cons k ks => simpa [hp0', Excl.admits, memB] using hadm
  have hu : l0.base ≠ u := by simpa [hb0] using hbu
  apply (loweredWith_iff hbu hu (by simpa [hl] using hu)).mpr
  refine ⟨hl, ?_⟩
  have hc := outside_field_not_cleaned_with (b := b) (reach := reach) (mark := mark) (m := l0.mark) hs
  cases l0 with
  | mk lb lp lm =>
    change lb = b at hb0
    subst lb
    exact hc

theorem outside_field_not_cleaned {b : Base} {g : Acc} {t m : Mark} {σ : List Acc}
    (hs : (Excl.set [g]).admits σ = true) :
    (fieldCleaner b g t).cleansB ⟨b, σ, m⟩ = false :=
  outside_field_not_cleaned_with hs

/-- Compatibility soundness theorem for the original cleaner API. -/
theorem backward_keep_record_sound {b u : Base} {g : Acc} {t : Mark} {l0 l : Loc}
    (hbu : b ≠ u)
    (hd : den (revRec ((coarse b).fact, backwardKeep b g)).1
      (revRec ((coarse b).fact, backwardKeep b g)).2.fact l0 l) :
    Lowered b u g t l0 l :=
  backward_keep_record_sound_with hbu hd

/-- Executable vectors test both the projected keep and surviving temporary branches. -/
def lowerKeepVector : Loc :=
  (lowerWitness 4 6 5 1 ⟨4, [4], 1⟩ (by decide) (by decide)).val
def lowerTempVector : Loc :=
  (lowerWitness 4 6 5 1 ⟨4, [5, 9], 2⟩ (by decide) (by decide)).val
def backwardKeepVector : AFact :=
  (backwardKeepWitness 4 6 5 1 (fun _ => true) 0 (by decide)).val

example : lowerKeepVector = ⟨4, [4], 1⟩ := by decide
example : lowerTempVector = ⟨6, [9], 2⟩ := by decide
example : backwardKeepVector = ⟨⟨4, [], .star (.set [5, 5]), .star⟩, false⟩ := by decide

/-- All six reach/mark-policy combinations used by the executable checks. -/
def reachPolicies : List (CleanReach × Option Mark) :=
  [(.exact, some 1), (.below, some 1), (.atAndBelow, some 1),
    (.exact, none), (.below, none), (.atAndBelow, none)]

/-- Probe both reach boundaries, both marks, and a sibling field. -/
def cleanReachVector (reach : CleanReach) (mark : Option Mark) : List Bool :=
  [⟨4, [5], 1⟩, ⟨4, [5, 9], 1⟩, ⟨4, [5], 2⟩,
    ⟨4, [5, 9], 2⟩, ⟨4, [4], 1⟩].map (fieldCleanerWith 4 5 reach mark).cleansB

def cleanReachVectors : List (List Bool) :=
  reachPolicies.map (fun p => cleanReachVector p.1 p.2)

/-- Each policy produces an executable middle witness for a surviving location. -/
def lowerReachVectors : List Loc :=
  [(lowerWitnessWith 4 6 5 .exact (some 1) ⟨4, [5, 9], 1⟩ (by decide) (by decide)).val,
    (lowerWitnessWith 4 6 5 .below (some 1) ⟨4, [5], 1⟩ (by decide) (by decide)).val,
    (lowerWitnessWith 4 6 5 .atAndBelow (some 1) ⟨4, [5, 9], 2⟩ (by decide) (by decide)).val,
    (lowerWitnessWith 4 6 5 .exact none ⟨4, [5, 9], 2⟩ (by decide) (by decide)).val,
    (lowerWitnessWith 4 6 5 .below none ⟨4, [5], 2⟩ (by decide) (by decide)).val,
    (lowerWitnessWith 4 6 5 .atAndBelow none ⟨4, [4], 1⟩ (by decide) (by decide)).val]

/-- Every policy yields the same executable AP backward keep witness. -/
def backwardKeepReachVectors : List AFact :=
  reachPolicies.map (fun p =>
    (backwardKeepWitnessWith 4 6 5 p.1 p.2 (fun _ => true) 0 (by decide)).val)

example : cleanReachVectors =
    [[true, false, false, false, false], [false, true, false, false, false],
      [true, true, false, false, false], [true, false, true, false, false],
      [false, true, false, true, false], [true, true, true, true, false]] := by decide
example : lowerReachVectors =
    [⟨6, [9], 1⟩, ⟨6, [], 1⟩, ⟨6, [9], 2⟩,
      ⟨6, [9], 2⟩, ⟨6, [], 2⟩, ⟨4, [4], 1⟩] := by decide
example : backwardKeepReachVectors = List.replicate 6 (backwardKeep 4 5) := by decide

#print axioms loweredWith_iff
#print axioms lowerWitnessWith
#print axioms lowerWitnessWith_val
#print axioms backward_keep_clean_with
#print axioms backwardKeepWitnessWith
#print axioms backwardKeepWitnessWith_val
#print axioms outside_field_not_cleaned_with
#print axioms backward_keep_record_sound_with
#print axioms lowered_iff
#print axioms lowerWitness
#print axioms backwardKeepWitness
#print axioms backward_keep_all_marks
#print axioms backward_keep_crossable
#print axioms backward_keep_record_sound
end ApSpec.CleanerLowering
