/-
  ApSpec.Core — the local lemmas of the AP operations: soundness of
  `applyEdge`, the statement transfer, the summary application, the field limit,
  the normal form, the start fact, the cover tests, the sink check and the
  request answer. The public lemmas are in `ApSpec`, the helpers in `ApSpec.CoreAux`.

  All proofs are constructive (audit with `#print axioms`).
-/
import ApSpec.Basic

namespace ApSpec.CoreAux
open ApSpec

/-! ## Booleans and accessor lists -/

theorem beq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem memB_iff {a : Acc} : ∀ {xs : List Acc}, memB a xs = true ↔ a ∈ xs
  | [] => ⟨fun h => Bool.noConfusion h, fun h => absurd h List.not_mem_nil⟩
  | b :: bs => by
    show (Nat.beq a b || memB a bs) = true ↔ a ∈ b :: bs
    rw [Bool.or_eq_true, List.mem_cons, beq_iff, memB_iff]

theorem memB_append {a : Acc} : ∀ {xs ys : List Acc},
    memB a (xs ++ ys) = (memB a xs || memB a ys)
  | [], _ => rfl
  | b :: bs, ys => by
    show (Nat.beq a b || memB a (bs ++ ys)) = ((Nat.beq a b || memB a bs) || memB a ys)
    rw [memB_append, Bool.or_assoc]

/-- If `a` is in `xs` and every element of `xs` is in `ys`, then `a` is in `ys`. -/
theorem memB_of_all {a : Acc} {ys : List Acc} : ∀ {xs : List Acc},
    memB a xs = true → xs.all (fun b => memB b ys) = true → memB a ys = true
  | [], h, _ => Bool.noConfusion h
  | b :: bs, h, hall => by
    have h' : (Nat.beq a b || memB a bs) = true := h
    have hall' : (memB b ys && bs.all (fun b => memB b ys)) = true := hall
    rw [Bool.and_eq_true] at hall'
    rw [Bool.or_eq_true] at h'
    cases h' with
    | inl hab => rw [beq_iff.mp hab]; exact hall'.1
    | inr hbs => exact memB_of_all hbs hall'.2

/-! ## Exclusions -/

theorem admits_nil (e : Excl) : e.admits [] = true := by
  cases e <;> rfl

theorem admits_append_cons (e : Excl) (a : Acc) (r s : List Acc) :
    e.admits (a :: r ++ s) = e.admits (a :: r) := by
  cases e <;> rfl

theorem empty_admits (σ : List Acc) : Excl.empty.admits σ = true := by
  cases σ <;> rfl

theorem univ_admits {σ : List Acc} : Excl.univ.admits σ = true → σ = [] := by
  cases σ with
  | nil => intro _; rfl
  | cons a s => intro h; exact Bool.noConfusion h

theorem Excl.admits_union (e1 e2 : Excl) (σ : List Acc) :
    (e1.union e2).admits σ = (e1.admits σ && e2.admits σ) := by
  cases σ with
  | nil => rw [admits_nil, admits_nil, admits_nil]; rfl
  | cons a s =>
    cases e1 with
    | univ => rfl
    | set xs =>
      cases e2 with
      | univ => show false = (!(memB a xs) && false); rw [Bool.and_false]
      | set ys =>
        show (!(memB a (xs ++ ys))) = (!(memB a xs) && !(memB a ys))
        rw [memB_append]
        cases memB a xs <;> cases memB a ys <;> rfl

theorem Excl.subB_sound {e1 e2 : Excl} {σ : List Acc} :
    e1.subB e2 = true → e2.admits σ = true → e1.admits σ = true := by
  intro hs ha
  cases σ with
  | nil => exact admits_nil e1
  | cons a s =>
    cases e2 with
    | univ => exact Bool.noConfusion ha
    | set ys =>
      cases e1 with
      | univ => exact Bool.noConfusion hs
      | set xs =>
        have ha' : (!(memB a ys)) = true := ha
        have hs' : xs.all (fun b => memB b ys) = true := hs
        show (!(memB a xs)) = true
        cases hm : memB a xs with
        | false => rfl
        | true =>
          have hy := memB_of_all hm hs'
          rw [hy] at ha'
          exact Bool.noConfusion ha'

theorem isEmptyB_admits {e : Excl} {σ : List Acc} : e.isEmptyB = true → e.admits σ = true := by
  intro h
  cases e with
  | univ => exact Bool.noConfusion h
  | set xs =>
    cases xs with
    | nil => exact empty_admits σ
    | cons _ _ => exact Bool.noConfusion h

/-! ## Tails -/

theorem admitsTailB_iff {k : Kind} {r : List Acc} : admitsTailB k r = true ↔ tailI k r := by
  cases k with
  | star e => exact Iff.rfl
  | any => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | exact =>
    cases r with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons a r => exact ⟨fun h => Bool.noConfusion h, fun h => (List.cons_ne_nil a r h).elim⟩

/-- A tail that admits `r ++ s` admits the prefix `r`. -/
theorem tailI_append_admits {k : Kind} {r s : List Acc} :
    tailI k (r ++ s) → admitsTailB k r = true := by
  intro h
  cases k with
  | star e =>
    cases r with
    | nil => exact admits_nil e
    | cons a r =>
      have h' : e.admits (a :: r ++ s) = true := h
      rw [admits_append_cons] at h'
      exact h'
  | any => rfl
  | exact =>
    cases r with
    | nil => rfl
    | cons a r => exact (List.cons_ne_nil a (r ++ s) h).elim

/-- A tail that admits a non-empty `a :: r` admits every extension of it. -/
theorem tailI_cons_append {k : Kind} {a : Acc} {r s : List Acc} :
    admitsTailB k (a :: r) = true → tailI k (a :: r ++ s) := by
  intro h
  cases k with
  | star e =>
    show e.admits (a :: r ++ s) = true
    rw [admits_append_cons]
    exact h
  | any => trivial
  | exact => exact Bool.noConfusion h

theorem tailI_of_tailF {k : Kind} {σ τ : List Acc} : tailF k σ τ → tailI k τ := by
  intro h
  cases k with
  | star e =>
    obtain ⟨h1, h2⟩ := h
    show e.admits τ = true
    rw [h1]
    exact h2
  | any => trivial
  | exact => exact h

theorem tailExcl_admits {k : Kind} {σ : List Acc} : tailI k σ → (tailExcl k).admits σ = true := by
  intro h
  cases k with
  | star e => exact h
  | any => exact empty_admits σ
  | exact =>
    have h' : σ = [] := h
    rw [h']
    exact admits_nil _

theorem tailSubB_sound {a b : Kind} {σ : List Acc} :
    tailSubB a b = true → tailI b σ → tailI a σ := by
  intro hs ht
  cases a with
  | star ea =>
    cases b with
    | star eb => exact Excl.subB_sound hs ht
    | any => exact isEmptyB_admits hs
    | exact =>
      have h' : σ = [] := ht
      show ea.admits σ = true
      rw [h']
      exact admits_nil ea
  | any => trivial
  | exact =>
    cases b with
    | star eb =>
      cases eb with
      | univ => exact univ_admits ht
      | set xs => exact Bool.noConfusion hs
    | any => exact Bool.noConfusion hs
    | exact => exact ht

/-! ## Marks -/

theorem admits_out (m : MarkA) (x : Mark) : m.admits (m.out x) := by
  cases m with
  | star => trivial
  | conc t => rfl

theorem out_of_admits {m : MarkA} {x : Mark} : m.admits x → x = m.out x := by
  intro h
  cases m with
  | star => rfl
  | conc t => exact h

theorem markOutA_out (a b : MarkA) (x : Mark) : (markOutA a b).out x = a.out (b.out x) := by
  cases a <;> rfl

theorem markOutA_conc {a : MarkA} {t : Mark} : ∃ t', markOutA a (.conc t) = .conc t' := by
  cases a with
  | star => exact ⟨t, rfl⟩
  | conc t' => exact ⟨t', rfl⟩

theorem markSubB_sound {a b : MarkA} {x : Mark} : markSubB a b = true → b.admits x → a.admits x := by
  intro hs hb
  cases a with
  | star => trivial
  | conc t =>
    cases b with
    | star => exact Bool.noConfusion hs
    | conc t' =>
      have h1 : x = t' := hb
      have h2 : t = t' := beq_iff.mp hs
      show x = t
      rw [h1, h2]

/-- The mark gate passes, or it asks for the mark `x` of a mark-abstract fact. -/
theorem gate_cases {fm cm : MarkA} {x : Mark} :
    fm.admits (cm.out x) → markGate fm cm = .ok ∨ (cm = .star ∧ markGate fm cm = .req x) := by
  intro h
  cases fm with
  | star => exact Or.inl rfl
  | conc t =>
    cases cm with
    | star =>
      have h' : x = t := h
      exact Or.inr ⟨rfl, by rw [h']; rfl⟩
    | conc t' =>
      have h' : t' = t := h
      left
      show (if Nat.beq t t' = true then Gate.ok else Gate.no) = Gate.ok
      rw [h', if_pos (Nat.beq_refl t)]

/-! ## Paths -/

theorem dropPrefix_some : ∀ {p q r : List Acc}, dropPrefix p q = some r ↔ q = p ++ r
  | [], q, r => by
    show some q = some r ↔ q = r
    exact ⟨Option.some.inj, fun h => h ▸ rfl⟩
  | a :: p, [], r => by
    show (none : Option (List Acc)) = some r ↔ [] = a :: (p ++ r)
    exact ⟨(fun h => nomatch h), (fun h => (List.cons_ne_nil a (p ++ r) h.symm).elim)⟩
  | a :: p, b :: q, r => by
    show (if Nat.beq a b = true then dropPrefix p q else none) = some r ↔ b :: q = a :: (p ++ r)
    cases hab : Nat.beq a b with
    | true =>
      rw [if_pos rfl, dropPrefix_some, beq_iff.mp hab]
      exact ⟨fun h => h ▸ rfl, fun h => List.cons.inj h |>.2⟩
    | false =>
      rw [if_neg Bool.false_ne_true]
      refine ⟨(fun h => nomatch h), (fun h => ?_)⟩
      have hba : b = a := (List.cons.inj h).1
      rw [hba, Nat.beq_refl] at hab
      exact Bool.noConfusion hab

theorem relate_below {P q r : List Acc} : dropPrefix P q = some r → relate P q = .below r := by
  intro h
  unfold relate
  rw [h]

theorem relate_above {P q r : List Acc} :
    dropPrefix P q = none → dropPrefix q P = some r → relate P q = .above r := by
  intro h1 h2
  unfold relate
  rw [h1, h2]

/-- Two paths with a common extension are related: one is a prefix of the other.
    `.above r` has `r ≠ []`. -/
theorem relate_common {P q σ τ : List Acc} (h : P ++ σ = q ++ τ) :
    (∃ r, relate P q = .below r ∧ q = P ++ r ∧ σ = r ++ τ) ∨
    (∃ r, relate P q = .above r ∧ P = q ++ r ∧ r ≠ [] ∧ τ = r ++ σ) := by
  cases hd : dropPrefix P q with
  | some r =>
    have hq := dropPrefix_some.mp hd
    left
    refine ⟨r, relate_below hd, hq, ?_⟩
    rw [hq, List.append_assoc] at h
    exact List.append_cancel_left h
  | none =>
    cases hd2 : dropPrefix q P with
    | some r =>
      have hP := dropPrefix_some.mp hd2
      right
      refine ⟨r, relate_above hd hd2, hP, ?_, ?_⟩
      · intro hr
        rw [hr, List.append_nil] at hP
        have h0 : dropPrefix P q = some [] := dropPrefix_some.mpr (by rw [hP, List.append_nil])
        rw [hd] at h0
        exact nomatch h0
      · rw [hP, List.append_assoc] at h
        exact (List.append_cancel_left h).symm
    | none =>
      exfalso
      rcases List.append_eq_append_iff.mp h with ⟨a', h1, _⟩ | ⟨c', h1, _⟩
      · have h0 := dropPrefix_some.mpr h1
        rw [hd] at h0
        exact nomatch h0
      · have h0 := dropPrefix_some.mpr h1
        rw [hd2] at h0
        exact nomatch h0

theorem cutPath_prefix {counted : Acc → Bool} :
    ∀ {n : Nat} {q p : List Acc}, cutPath counted n q = some p → ∃ s, q = p ++ s
  | _, [], _, h => nomatch h
  | n, a :: as, p, h => by
    have hmap : ∀ {m : Nat} {p : List Acc},
        (cutPath counted m as).map (a :: ·) = some p → ∃ s, a :: as = p ++ s := by
      intro m p hm
      cases hc : cutPath counted m as with
      | none => rw [hc] at hm; exact nomatch hm
      | some p' =>
        rw [hc] at hm
        have hp : a :: p' = p := Option.some.inj hm
        obtain ⟨s, hs⟩ := cutPath_prefix hc
        exact ⟨s, by rw [← hp, hs]; rfl⟩
    unfold cutPath at h
    cases hca : counted a with
    | true =>
      rw [hca, if_pos rfl] at h
      cases n with
      | zero =>
        have hp : [] = p := Option.some.inj h
        exact ⟨a :: as, by rw [← hp]; rfl⟩
      | succ m => exact hmap h
    | false =>
      rw [hca, if_neg Bool.false_ne_true] at h
      exact hmap h

/-! ## The geometry of `applyEdge` -/

/-- The geometric part of `applyEdge` (before the mark gate). -/
def geo (ck fk : Kind) (P q toPath : List Acc) (tk : Kind) : Option (List Acc × Kind × Bool) :=
  match relate P q with
  | .below r => belowCase ck fk r toPath tk
  | .above r => aboveCase ck fk r toPath tk
  | .apart   => none

/-- The result of `applyEdge` for a given gate. -/
def finG (c : AFact) (to : PFact) (p : List Acc) (k : Kind) (ap : Bool) : Gate → Res
  | .no    => Res.none
  | .req t => ⟨[], [t]⟩
  | .ok    => ⟨[AFact.norm ⟨⟨to.base, p, k, markOutA to.mark c.fact.mark⟩, c.demand || ap⟩], []⟩

/-- The result of `applyEdge` for a given geometric result. -/
def fin (c : AFact) (fr to : PFact) : Option (List Acc × Kind × Bool) → Res
  | none => Res.none
  | some (p, k, ap) => finG c to p k ap (markGate fr.mark c.fact.mark)

/-- The normal form keeps the base, the path and the mark. -/
theorem norm_mark (f : AFact) : f.norm.fact.mark = f.fact.mark := by
  obtain ⟨⟨b, p, k, m⟩, ap⟩ := f
  unfold AFact.norm
  cases k with
  | star e =>
    cases m with
    | star => cases ap <;> cases e <;> rfl
    | conc t => cases e <;> rfl
  | any => rfl
  | exact => rfl

/-- The normal form only enlarges a fact. -/
theorem norm_sound {i : PFact} {f : AFact} {l0 l1 : Loc} :
    den i f.fact l0 l1 → den i f.norm.fact l0 l1 := by
  intro h
  obtain ⟨⟨b, p, k, m⟩, ap⟩ := f
  obtain ⟨hb0, hb1, hm0, hm1, σ, τ, hp0, hp1, hti, htf⟩ := h
  have hstar : ∀ k', (∀ σ τ, tailF k σ τ → tailF k' σ τ) →
      den i ⟨b, p, k', m⟩ l0 l1 :=
    fun k' hk => ⟨hb0, hb1, hm0, hm1, σ, τ, hp0, hp1, hti, hk σ τ htf⟩
  unfold AFact.norm
  cases k with
  | star e =>
    have hex : ∀ σ τ, tailF (.star Excl.univ) σ τ → tailF .exact σ τ := by
      intro σ τ h
      obtain ⟨hτ, hu⟩ := h
      cases σ with
      | nil => exact hτ
      | cons a r => exact absurd hu (by simp only [Excl.admits]; decide)
    have hany : ∀ k0 : Kind, ∀ σ τ, tailF k0 σ τ → tailF .any σ τ := fun _ _ _ _ => trivial
    cases m with
    | star =>
      cases ap with
      | false => cases e <;> exact ⟨hb0, hb1, hm0, hm1, σ, τ, hp0, hp1, hti, htf⟩
      | true =>
        cases e with
        | univ => exact hstar .exact (hex)
        | set xs => exact hstar .any (hany _)
    | conc t =>
      cases e with
      | univ => exact hstar .exact (hex)
      | set xs => exact hstar .any (hany _)
  | any => exact ⟨hb0, hb1, hm0, hm1, σ, τ, hp0, hp1, hti, htf⟩
  | exact => exact ⟨hb0, hb1, hm0, hm1, σ, τ, hp0, hp1, hti, htf⟩

theorem applyEdge_eq (c : AFact) (fr to : PFact) :
    applyEdge c fr to =
      if Nat.beq c.fact.base fr.base then
        fin c fr to (geo c.fact.kind fr.kind fr.path c.fact.path to.path to.kind)
      else Res.none := by
  unfold applyEdge fin geo
  rfl

theorem fin_some (c : AFact) (fr to : PFact) (p : List Acc) (k : Kind) (ap : Bool) :
    fin c fr to (some (p, k, ap)) = finG c to p k ap (markGate fr.mark c.fact.mark) := rfl

/-- Case `below r`. -/
theorem below_sound {ck fk tk : Kind} {r toPath σ τ τ' : List Acc}
    (hc : tailF ck σ τ) (hf : tailI fk (r ++ τ)) (ht : tailF tk (r ++ τ) τ') :
    ∃ p k ap, belowCase ck fk r toPath tk = some (p, k, ap) ∧
      ∃ τ'', toPath ++ τ' = p ++ τ'' ∧ tailF k σ τ'' := by
  have hadm : admitsTailB fk r = true := tailI_append_admits hf
  unfold belowCase
  rw [if_pos hadm]
  cases tk with
  | star et =>
    obtain ⟨hτ', het⟩ := ht
    cases r with
    | cons a r =>
      have ha : et.admits (a :: r) = true := by
        rw [← admits_append_cons et a r τ]; exact het
      refine ⟨toPath ++ a :: r, ck, false, ?_, τ, ?_, hc⟩
      · show (if et.admits (a :: r) = true then _ else _) = _
        rw [if_pos ha]
      · rw [hτ', List.append_assoc]
    | nil =>
      have het' : et.admits τ = true := het
      have hτ'' : τ' = τ := hτ'
      have hf' : tailI fk τ := hf
      have hex : ((tailExcl fk).union et).admits τ = true := by
        rw [Excl.admits_union, tailExcl_admits hf', het']; rfl
      cases ck with
      | exact =>
        have hc' : τ = [] := hc
        refine ⟨toPath, .exact, false, rfl, [], ?_, rfl⟩
        rw [hτ'', hc']
      | star ec =>
        obtain ⟨hc1, hc2⟩ := hc
        refine ⟨toPath, .star (ec.union ((tailExcl fk).union et)), false, rfl, τ, ?_, hc1, ?_⟩
        · rw [hτ'']
        · rw [Excl.admits_union, ← hc1, hex, hc1, hc2]; rfl
      | any =>
        cases hx : (tailExcl fk).union et with
        | univ =>
          rw [hx] at hex
          refine ⟨toPath, .exact, false, ?_, [], ?_, rfl⟩
          · simp only [hx]
          · rw [hτ'', univ_admits hex]
        | set xs =>
          refine ⟨toPath, .any, !(Excl.set xs).isEmptyB, ?_, τ', rfl, trivial⟩
          simp only [hx]
  | any =>
    exact ⟨toPath, .any, lostCorr ck fk r, rfl, τ', rfl, trivial⟩
  | exact =>
    have ht' : τ' = [] := ht
    cases ck with
    | star ec =>
      cases fk with
      | exact =>
        cases r with
        | nil =>
          have hf' : τ = [] := hf
          refine ⟨toPath, .star .univ, false, rfl, [], by rw [ht'], ?_⟩
          have hσ : σ = [] := by rw [← hc.1]; exact hf'
          exact ⟨hσ.symm, by rw [hσ]; rfl⟩
        | cons a r => exact ⟨toPath, .exact, lostCorr (.star ec) .exact (a :: r), rfl, [], by rw [ht'], rfl⟩
      | star e => exact ⟨toPath, .exact, lostCorr (.star ec) (.star e) r, rfl, [], by rw [ht'], rfl⟩
      | any => exact ⟨toPath, .exact, lostCorr (.star ec) .any r, rfl, [], by rw [ht'], rfl⟩
    | any => exact ⟨toPath, .exact, false, rfl, [], by rw [ht'], rfl⟩
    | exact => exact ⟨toPath, .exact, false, rfl, [], by rw [ht'], rfl⟩

/-- Case `above r` (r ≠ []). -/
theorem above_sound {ck fk tk : Kind} {r toPath σ σ' τ' : List Acc} (hr : r ≠ [])
    (hc : tailF ck σ (r ++ σ')) (ht : tailF tk σ' τ') :
    ∃ p k ap, aboveCase ck fk r toPath tk = some (p, k, ap) ∧
      ∃ τ'', toPath ++ τ' = p ++ τ'' ∧ tailF k σ τ'' := by
  have hadm : admitsTailB ck r = true := by
    cases ck with
    | star e =>
      obtain ⟨h1, h2⟩ := hc
      rw [← h1] at h2
      exact tailI_append_admits (k := .star e) h2
    | any => rfl
    | exact =>
      have hc' : r ++ σ' = [] := hc
      cases r with
      | nil => exact absurd rfl hr
      | cons a r => exact (List.cons_ne_nil a (r ++ σ') hc').elim
  unfold aboveCase
  rw [if_pos hadm]
  cases tk with
  | star et => exact ⟨toPath, .any, _, rfl, τ', rfl, trivial⟩
  | any => exact ⟨toPath, .any, _, rfl, τ', rfl, trivial⟩
  | exact =>
    have ht' : τ' = [] := ht
    exact ⟨toPath, .exact, _, rfl, [], by rw [ht'], rfl⟩

/-- The geometry of `applyEdge` is sound: an overlap gives a result that
    covers the composed continuation. -/
theorem geo_sound {ck fk tk : Kind} {P q toPath σ τ σ' τ' : List Acc}
    (h : q ++ τ = P ++ σ') (hc : tailF ck σ τ) (hf : tailI fk σ') (ht : tailF tk σ' τ') :
    ∃ p k ap, geo ck fk P q toPath tk = some (p, k, ap) ∧
      ∃ τ'', toPath ++ τ' = p ++ τ'' ∧ tailF k σ τ'' := by
  rcases relate_common h.symm with ⟨r, hrel, _, hσ'⟩ | ⟨r, hrel, _, hr, hτ⟩
  · unfold geo
    rw [hrel]
    rw [hσ'] at hf ht
    exact below_sound hc hf ht
  · unfold geo
    rw [hrel]
    rw [hτ] at hc
    exact above_sound hr hc ht

/-- The result fact of the `ok` gate covers the composed pair. -/
theorem den_result {ic to : PFact} {cm : MarkA} {p : List Acc} {k : Kind} {l0 l1 l2 : Loc}
    {σ τ'' : List Acc}
    (hb0 : l0.base = ic.base) (hm0 : ic.mark.admits l0.mark) (hm1 : l1.mark = cm.out l0.mark)
    (hb2 : l2.base = to.base) (hm2 : l2.mark = to.mark.out l1.mark)
    (hp0 : l0.path = ic.path ++ σ) (hti : tailI ic.kind σ)
    (hp2 : l2.path = p ++ τ'') (htf : tailF k σ τ'') :
    den ic ⟨to.base, p, k, markOutA to.mark cm⟩ l0 l2 :=
  ⟨hb0, hb2, hm0, by rw [hm2, hm1, markOutA_out], σ, τ'', hp0, hp2, hti, htf⟩

theorem mem_applyEdge_facts {c r : AFact} {fr to : PFact} :
    r ∈ (applyEdge c fr to).facts → r.fact.mark = markOutA to.mark c.fact.mark := by
  intro h
  rw [applyEdge_eq] at h
  cases hb : Nat.beq c.fact.base fr.base with
  | false =>
    rw [hb, if_neg Bool.false_ne_true] at h
    exact absurd h List.not_mem_nil
  | true =>
    rw [hb, if_pos rfl] at h
    cases hg : geo c.fact.kind fr.kind fr.path c.fact.path to.path to.kind with
    | none =>
      rw [hg] at h
      exact absurd h List.not_mem_nil
    | some x =>
      obtain ⟨p, k, ap⟩ := x
      rw [hg, fin_some] at h
      cases hgt : markGate fr.mark c.fact.mark with
      | ok =>
        rw [hgt] at h
        have hr := List.mem_singleton.mp h
        rw [hr, norm_mark]
      | no =>
        rw [hgt] at h
        exact absurd h List.not_mem_nil
      | req t =>
        rw [hgt] at h
        exact absurd h List.not_mem_nil

theorem reqs_of_gate {c : AFact} {fr to : PFact} :
    (∀ t, markGate fr.mark c.fact.mark ≠ .req t) → (applyEdge c fr to).reqs = [] := by
  intro hn
  rw [applyEdge_eq]
  cases hb : Nat.beq c.fact.base fr.base with
  | false => rw [if_neg Bool.false_ne_true]; rfl
  | true =>
    rw [if_pos rfl]
    cases hg : geo c.fact.kind fr.kind fr.path c.fact.path to.path to.kind with
    | none => rfl
    | some x =>
      obtain ⟨p, k, ap⟩ := x
      rw [fin_some]
      cases hgt : markGate fr.mark c.fact.mark with
      | ok => rfl
      | no => rfl
      | req t => exact absurd hgt (hn t)

end ApSpec.CoreAux

namespace ApSpec

/-- A final fact covers the end location of each of its pairs. -/
theorem den_covers_final {i f : PFact} {l0 l1 : Loc} :
    den i f l0 l1 → f.covers l1 := by
  intro h
  obtain ⟨_, hb1, _, hm1, σ, τ, _, hp1, _, htf⟩ := h
  refine ⟨hb1, ⟨τ, hp1, CoreAux.tailI_of_tailF htf⟩, ?_⟩
  rw [hm1]
  exact CoreAux.admits_out f.mark l0.mark

/-- The start fact covers the identity on the location set of the initial fact. -/
theorem startFact_sound {i : PFact} {l0 : Loc} :
    i.covers l0 → den i (startFact i).fact l0 l0 := by
  obtain ⟨ib, ip, ik, im⟩ := i
  intro h
  obtain ⟨hb, ⟨σ, hp, ht⟩, hm⟩ := h
  have hmo : l0.mark = im.out l0.mark := CoreAux.out_of_admits hm
  cases ik with
  | star e =>
    cases im with
    | star => exact ⟨hb, hb, hm, hmo, σ, σ, hp, hp, ht, rfl, ht⟩
    | conc t => exact ⟨hb, hb, hm, hmo, σ, σ, hp, hp, ht, trivial⟩
  | any =>
    cases im with
    | star => exact ⟨hb, hb, hm, hmo, σ, σ, hp, hp, ht, trivial⟩
    | conc t => exact ⟨hb, hb, hm, hmo, σ, σ, hp, hp, ht, trivial⟩
  | exact =>
    cases im with
    | star => exact ⟨hb, hb, hm, hmo, σ, σ, hp, hp, ht, ht⟩
    | conc t => exact ⟨hb, hb, hm, hmo, σ, σ, hp, hp, ht, ht⟩

theorem startFact_mark {i : PFact} : (startFact i).fact.mark = i.mark := by
  obtain ⟨ib, ip, ik, im⟩ := i
  cases ik <;> cases im <;> rfl

/-- The field limit only enlarges a fact. -/
theorem limitF_sound {counted : Acc → Bool} {L : Nat} {i : PFact} {f : AFact} {l0 l1 : Loc} :
    den i f.fact l0 l1 → den i (limitF counted L f).fact l0 l1 := by
  intro h
  unfold limitF
  cases hc : cutPath counted L f.fact.path with
  | none => exact h
  | some p =>
    obtain ⟨hb0, hb1, hm0, hm1, σ, τ, hp0, hp1, hti, _⟩ := h
    obtain ⟨s, hs⟩ := CoreAux.cutPath_prefix hc
    refine ⟨hb0, hb1, hm0, hm1, σ, s ++ τ, hp0, ?_, hti, trivial⟩
    rw [hp1, hs, List.append_assoc]

/-- THE CORE LEMMA. `applyEdge` covers the composition of the fact relation and
    the edge relation, or it raises the request for the mark that the premise needs. -/
theorem applyEdge_sound {ic fr to : PFact} {c : AFact} {l0 l1 l2 : Loc} :
    den ic c.fact l0 l1 → den fr to l1 l2 →
    (∃ r, r ∈ (applyEdge c fr to).facts ∧ den ic r.fact l0 l2) ∨
    (c.fact.mark = .star ∧ l0.mark ∈ (applyEdge c fr to).reqs) := by
  intro h1 h2
  obtain ⟨hb0, hb1, hm0, hm1, σ, τ, hp0, hp1, hti, htf⟩ := h1
  obtain ⟨hb1', hb2, hm1', hm2, σ', τ', hp1', hp2, hti', htf'⟩ := h2
  have hbase : Nat.beq c.fact.base fr.base = true := by
    rw [← hb1, hb1']; exact Nat.beq_refl _
  have hpath : c.fact.path ++ τ = fr.path ++ σ' := by rw [← hp1, hp1']
  obtain ⟨p, k, ap, hgeo, τ'', hp2'', htf''⟩ :=
    CoreAux.geo_sound (toPath := to.path) hpath htf hti' htf'
  rw [CoreAux.applyEdge_eq, if_pos hbase, hgeo, CoreAux.fin_some]
  have hadm : fr.mark.admits (c.fact.mark.out l0.mark) := by rw [← hm1]; exact hm1'
  rcases CoreAux.gate_cases hadm with hg | ⟨hcs, hg⟩
  · rw [hg]
    left
    exact ⟨AFact.norm ⟨⟨to.base, p, k, markOutA to.mark c.fact.mark⟩, c.demand || ap⟩,
      List.mem_singleton.mpr rfl,
      CoreAux.norm_sound (CoreAux.den_result hb0 hm0 hm1 hb2 hm2 hp0 hti (by rw [hp2, hp2'']) htf'')⟩
  · rw [hg]
    right
    exact ⟨hcs, List.mem_singleton.mpr rfl⟩

/-- A mark-agnostic premise raises no request. -/
theorem applyEdge_reqs_of_star {c : AFact} {fr to : PFact} :
    fr.mark = .star → (applyEdge c fr to).reqs = [] := by
  intro h
  apply CoreAux.reqs_of_gate
  intro t ht
  rw [h] at ht
  exact Gate.noConfusion ht

/-- A concrete mark stays concrete. -/
theorem applyEdge_mark_conc {c r : AFact} {fr to : PFact} {t : Mark} :
    c.fact.mark = .conc t → r ∈ (applyEdge c fr to).facts → ∃ t', r.fact.mark = .conc t' := by
  intro hc hr
  rw [CoreAux.mem_applyEdge_facts hr, hc]
  exact CoreAux.markOutA_conc

/-- No request comes from a fact with a concrete mark. -/
theorem applyEdge_reqs_of_conc {c : AFact} {fr to : PFact} {t : Mark} :
    c.fact.mark = .conc t → (applyEdge c fr to).reqs = [] := by
  intro hc
  apply CoreAux.reqs_of_gate
  intro t' ht
  rw [hc] at ht
  cases hm : fr.mark with
  | star => rw [hm] at ht; exact Gate.noConfusion ht
  | conc t0 =>
    rw [hm] at ht
    have ht' : (if Nat.beq t0 t = true then Gate.ok else Gate.no) = Gate.req t' := ht
    cases hq : Nat.beq t0 t with
    | true => rw [hq, if_pos rfl] at ht'; exact Gate.noConfusion ht'
    | false => rw [hq, if_neg Bool.false_ne_true] at ht'; exact Gate.noConfusion ht'

/-- Summary application is `applyEdge` with the layer of the summary edge added. -/
theorem applySummary_sound {ic j : PFact} {a g : AFact} {l0 l1 l2 : Loc} :
    den ic a.fact l0 l1 → den j g.fact l1 l2 →
    (∃ r, r ∈ (applySummary a j g).facts ∧ den ic r.fact l0 l2) ∨
    (a.fact.mark = .star ∧ l0.mark ∈ (applySummary a j g).reqs) := by
  intro h1 h2
  rcases applyEdge_sound h1 h2 with ⟨r, hr, hd⟩ | ⟨hs, hreq⟩
  · left
    exact ⟨AFact.norm ⟨r.fact, r.demand || g.demand⟩,
      List.mem_map_of_mem (f := fun x : AFact => AFact.norm (⟨x.fact, x.demand || g.demand⟩ : AFact)) hr,
      CoreAux.norm_sound (f := ⟨r.fact, r.demand || g.demand⟩) hd⟩
  · right
    exact ⟨hs, hreq⟩

theorem applySummary_mark_conc {a g r : AFact} {j : PFact} {t : Mark} :
    a.fact.mark = .conc t → r ∈ (applySummary a j g).facts → ∃ t', r.fact.mark = .conc t' := by
  intro ha hr
  obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hr
  rw [← hxr, CoreAux.norm_mark]
  obtain ⟨t', ht'⟩ := applyEdge_mark_conc ha hx
  exact ⟨t', ht'⟩

theorem limitF_mark {counted : Acc → Bool} {L : Nat} {f : AFact} :
    (limitF counted L f).fact.mark = f.fact.mark := by
  unfold limitF
  cases cutPath counted L f.fact.path <;> rfl

end ApSpec

namespace ApSpec.CoreAux
open ApSpec

theorem mem_applyAll_facts {c r : AFact} {e : MicroEdge} :
    ∀ {es : List MicroEdge}, e ∈ es → r ∈ (applyEdge c e.1 e.2).facts → r ∈ (applyAll c es).facts
  | [], he, _ => absurd he List.not_mem_nil
  | e' :: es, he, hr => by
    show r ∈ (applyEdge c e'.1 e'.2).facts ++ (applyAll c es).facts
    rcases List.mem_cons.mp he with he' | he'
    · rw [← he']; exact List.mem_append.mpr (Or.inl hr)
    · exact List.mem_append.mpr (Or.inr (mem_applyAll_facts he' hr))

theorem mem_applyAll_reqs {c : AFact} {e : MicroEdge} {t : Mark} :
    ∀ {es : List MicroEdge}, e ∈ es → t ∈ (applyEdge c e.1 e.2).reqs → t ∈ (applyAll c es).reqs
  | [], he, _ => absurd he List.not_mem_nil
  | e' :: es, he, hr => by
    show t ∈ (applyEdge c e'.1 e'.2).reqs ++ (applyAll c es).reqs
    rcases List.mem_cons.mp he with he' | he'
    · rw [← he']; exact List.mem_append.mpr (Or.inl hr)
    · exact List.mem_append.mpr (Or.inr (mem_applyAll_reqs he' hr))

theorem applyAll_facts_inv {c r : AFact} :
    ∀ {es : List MicroEdge}, r ∈ (applyAll c es).facts →
      ∃ e, e ∈ es ∧ r ∈ (applyEdge c e.1 e.2).facts
  | [], h => absurd h List.not_mem_nil
  | e' :: es, h => by
    have h' : r ∈ (applyEdge c e'.1 e'.2).facts ++ (applyAll c es).facts := h
    rcases List.mem_append.mp h' with h1 | h1
    · exact ⟨e', List.mem_cons_self, h1⟩
    · obtain ⟨e, he, hr⟩ := applyAll_facts_inv h1
      exact ⟨e, List.mem_cons_of_mem _ he, hr⟩

theorem applyAll_reqs_of_conc {c : AFact} {t : Mark} (hc : c.fact.mark = .conc t) :
    ∀ {es : List MicroEdge}, (applyAll c es).reqs = []
  | [] => rfl
  | e' :: es => by
    show (applyEdge c e'.1 e'.2).reqs ++ (applyAll c es).reqs = []
    rw [applyEdge_reqs_of_conc hc, applyAll_reqs_of_conc hc]
    rfl


/-- The sink check after the mark and overlap tests pass. -/
def checkIn (i : PFact) (f : AFact) (T : Mark) : Check :=
  match f.fact.mark with
  | .conc t => if Nat.beq t T then .triggered else .none
  | .star   =>
    match i.mark with
    | .conc t => if Nat.beq t T then .triggered else .none
    | .star   => .request T

theorem check_eq_in {i s : PFact} {f : AFact} {T : Mark} :
    s.mark = .conc T → overlapB f.fact s = true → check i f s = checkIn i f T := by
  intro hs ho
  unfold check
  rw [hs]
  show (if overlapB f.fact s = true then _ else _) = _
  rw [if_pos ho]
  rfl

end ApSpec.CoreAux

namespace ApSpec

/-- Statement transfer covers the statement step (needs the WF condition that
    every micro edge reads from a touched base). -/
theorem transfer_sound {counted : Acc → Bool} {L : Nat} {s : Stmt} {ic : PFact} {c : AFact}
    {l0 l l' : Loc} :
    (∀ e, e ∈ s.edges → memB e.1.base s.touched = true) →
    den ic c.fact l0 l → s.step l l' →
    (∃ r, r ∈ (transfer counted L s c).facts ∧ den ic r.fact l0 l') ∨
    (c.fact.mark = .star ∧ l0.mark ∈ (transfer counted L s c).reqs) := by
  intro hwf hden hstep
  have hb : l.base = c.fact.base := hden.2.1
  unfold transfer
  cases hm : memB c.fact.base s.touched with
  | false =>
    rw [if_neg Bool.false_ne_true]
    rcases hstep with ⟨_, hl⟩ | ⟨e, he, hde⟩
    · left
      rw [hl]
      exact ⟨c, List.mem_singleton.mpr rfl, hden⟩
    · exfalso
      have h1 := hwf e he
      rw [← hde.1, hb, hm] at h1
      exact Bool.noConfusion h1
  | true =>
    rw [if_pos rfl]
    rcases hstep with ⟨hnt, _⟩ | ⟨e, he, hde⟩
    · exfalso
      rw [hb, hm] at hnt
      exact Bool.noConfusion hnt
    · rcases applyEdge_sound hden hde with ⟨r, hr, hd⟩ | ⟨hs, hreq⟩
      · left
        exact ⟨limitF counted L r,
          List.mem_map_of_mem (CoreAux.mem_applyAll_facts he hr), limitF_sound hd⟩
      · right
        exact ⟨hs, CoreAux.mem_applyAll_reqs he hreq⟩

theorem transfer_mark_conc {counted : Acc → Bool} {L : Nat} {s : Stmt} {c r : AFact} {t : Mark} :
    c.fact.mark = .conc t → r ∈ (transfer counted L s c).facts → ∃ t', r.fact.mark = .conc t' := by
  intro hc hr
  unfold transfer at hr
  cases hm : memB c.fact.base s.touched with
  | false =>
    rw [hm, if_neg Bool.false_ne_true] at hr
    rw [List.mem_singleton.mp hr]
    exact ⟨t, hc⟩
  | true =>
    rw [hm, if_pos rfl] at hr
    obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hr
    obtain ⟨e, _, hxe⟩ := CoreAux.applyAll_facts_inv hx
    rw [← hxr, limitF_mark]
    exact applyEdge_mark_conc hc hxe

theorem transfer_reqs_of_conc {counted : Acc → Bool} {L : Nat} {s : Stmt} {c : AFact} {t : Mark} :
    c.fact.mark = .conc t → (transfer counted L s c).reqs = [] := by
  intro hc
  unfold transfer
  cases hm : memB c.fact.base s.touched with
  | false => rw [if_neg Bool.false_ne_true]
  | true =>
    rw [if_pos rfl]
    exact CoreAux.applyAll_reqs_of_conc hc

/-- The syntactic cover test is sound. -/
theorem coversB_sound {i c : PFact} {l : Loc} :
    coversB i c = true → c.covers l → i.covers l := by
  intro h hc
  obtain ⟨hb, ⟨σ, hp, ht⟩, hm⟩ := hc
  unfold coversB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hb', hms⟩, hd⟩ := h
  refine ⟨by rw [hb, CoreAux.beq_iff.mp hb'], ?_, CoreAux.markSubB_sound hms hm⟩
  cases hdp : dropPrefix i.path c.path with
  | none =>
    rw [hdp] at hd
    exact Bool.noConfusion hd
  | some r =>
    have hcp := CoreAux.dropPrefix_some.mp hdp
    rw [hdp] at hd
    cases r with
    | nil =>
      refine ⟨σ, ?_, CoreAux.tailSubB_sound hd ht⟩
      rw [hp, hcp, List.append_nil]
    | cons a r =>
      refine ⟨a :: r ++ σ, ?_, CoreAux.tailI_cons_append hd⟩
      rw [hp, hcp, List.append_assoc]

theorem applicable_sound {i c : PFact} {l : Loc} :
    applicable i c = true → c.covers l → i.covers l := by
  intro h hc
  unfold applicable at h
  rw [Bool.and_eq_true] at h
  exact coversB_sound h.1 hc

/-- An applicable premise with a concrete mark forces the same concrete mark. -/
theorem applicable_mark {i c : PFact} {t : Mark} :
    applicable i c = true → i.mark = .conc t → c.mark = .conc t := by
  intro h hi
  unfold applicable coversB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  have hms := h.1.1.2
  rw [hi] at hms
  cases hc : c.mark with
  | star => rw [hc] at hms; exact Bool.noConfusion hms
  | conc t' =>
    rw [hc] at hms
    have h' : Nat.beq t t' = true := hms
    rw [CoreAux.beq_iff.mp h']

/-- Two facts with a common location overlap. -/
theorem overlapB_of_common {a b : PFact} {l : Loc} :
    a.covers l → b.covers l → overlapB a b = true := by
  intro ha hb
  obtain ⟨hba, ⟨σa, hpa, hta⟩, _⟩ := ha
  obtain ⟨hbb, ⟨σb, hpb, htb⟩, _⟩ := hb
  unfold overlapB
  rw [Bool.and_eq_true]
  refine ⟨by rw [← hba, ← hbb]; exact Nat.beq_refl _, ?_⟩
  have h : a.path ++ σa = b.path ++ σb := by rw [← hpa, ← hpb]
  rcases CoreAux.relate_common h with ⟨r, hrel, _, hσ⟩ | ⟨r, hrel, _, _, hτ⟩
  · rw [hrel]
    rw [hσ] at hta
    exact CoreAux.tailI_append_admits hta
  · rw [hrel]
    rw [hτ] at htb
    exact CoreAux.tailI_append_admits htb

theorem subB_refl (e : Excl) : e.subB e = true := by
  cases e with
  | univ => rfl
  | set xs =>
    show xs.all (fun a => memB a xs) = true
    exact List.all_eq_true.mpr (fun a ha => CoreAux.memB_iff.mpr ha)

theorem tailSubB_refl (k : Kind) : tailSubB k k = true := by
  cases k with
  | star e => exact subB_refl e
  | any => rfl
  | exact => rfl

/-- The answer of a request covers the requested location with the requested mark. -/
theorem answerInit_covers {i a : PFact} {t : Mark} {l : Loc} :
    i.covers l → a.covers l → l.mark = t → (answerInit i a t).covers l := by
  intro hi ha hm
  obtain ⟨hbi, hpi, _⟩ := hi
  unfold answerInit
  split
  · rename_i hk hd
    obtain ⟨_, ⟨σ, hp, ht⟩, _⟩ := ha
    rw [hk] at ht
    have hσ : σ = [] := ht
    have hap := CoreAux.dropPrefix_some.mp hd
    exact ⟨hbi, ⟨[], by simp only [hp, hσ, hap, List.append_nil], rfl⟩, hm⟩
  · exact ⟨hbi, hpi, hm⟩

theorem answerInit_applicable {i a : PFact} {t : Mark} :
    applicable i a = true → a.mark = .conc t → applicable (answerInit i a t) a = true := by
  intro happ ham
  have happ' := happ
  unfold applicable coversB at happ'
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at happ'
  obtain ⟨⟨⟨hb, _⟩, hd⟩, hn⟩ := happ'
  have hms : markSubB (.conc t) a.mark = true := by rw [ham]; exact Nat.beq_refl t
  unfold answerInit
  split
  · rename_i hk hdp
    unfold applicable coversB
    rw [hb, hms, hdp, hk]
    rfl
  · unfold applicable coversB
    rw [hb, hms, hd, hn]
    rfl

theorem answerInit_mark {i a : PFact} {t : Mark} :
    (answerInit i a t).mark = .conc t := by
  unfold answerInit
  split <;> rfl

/-- The abstraction policy satisfies the contract (A1). -/
theorem policy_applicable (demand : MethodId → List PFact) (m : MethodId) (a : PFact) :
    applicable (policy demand m a) a = true := by
  unfold policy
  by_cases hz : a = zeroFact
  · rw [if_pos hz, hz]; rfl
  · rw [if_neg hz]
    have hcov : ∀ p : List Acc, dropPrefix p a.path ≠ none →
        applicable ⟨a.base, p, .star Excl.empty, .star⟩ a = true := by
      intro p hp
      unfold applicable coversB
      cases hd : dropPrefix p a.path with
      | none => exact absurd hd hp
      | some r =>
        have hk : tailSubB (.star Excl.empty) a.kind = true := by
          cases a.kind with
          | star e => cases e <;> rfl
          | any => rfl
          | exact => rfl
        cases r with
        | nil => simp only [Nat.beq_refl, markSubB, hk, Kind.isAny, Bool.not_false, Bool.true_or, Bool.and_self]
        | cons x r' => simp only [Nat.beq_refl, markSubB, admitsTailB, Excl.empty, Excl.admits, memB, Bool.not_false, Kind.isAny, Bool.true_or, Bool.and_self]
    have hself : dropPrefix a.path a.path ≠ none := by
      rw [CoreAux.dropPrefix_some.mpr (List.append_nil a.path).symm]; intro h; cases h
    have hroot : dropPrefix [] a.path ≠ none := by
      show some a.path ≠ none; intro h; cases h
    by_cases hd : (demand m).any (fun d => overlapB d a) = true
    · rw [if_pos hd]; exact hcov _ hself
    · rw [if_neg hd]; exact hcov _ hroot

/-- The sink check is sound: a covered tainted location triggers the sink, or
    raises the request for the sink mark on a mark-abstract initial fact. -/
theorem check_sound {i s : PFact} {f : AFact} {l0 l : Loc} {T : Mark} :
    s.mark = .conc T → den i f.fact l0 l → s.covers l →
    check i f s = .triggered ∨ (check i f s = .request l0.mark ∧ i.mark = .star) := by
  intro hsm hden hs
  have hov : overlapB f.fact s = true := overlapB_of_common (den_covers_final hden) hs
  have hlT : l.mark = T := by
    have h := hs.2.2
    rw [hsm] at h
    exact h
  obtain ⟨_, _, hm0, hm1, _⟩ := hden
  rw [CoreAux.check_eq_in hsm hov]
  unfold CoreAux.checkIn
  cases hf : f.fact.mark with
  | conc t' =>
    rw [hf] at hm1
    have ht : t' = T := by rw [← hlT, hm1]; rfl
    left
    show (if Nat.beq t' T = true then Check.triggered else Check.none) = Check.triggered
    rw [ht, if_pos (Nat.beq_refl T)]
  | star =>
    rw [hf] at hm1
    have h0 : l0.mark = T := by rw [← hlT, hm1]; rfl
    cases hi : i.mark with
    | conc t' =>
      rw [hi] at hm0
      have ht : t' = T := by rw [← h0]; exact hm0.symm
      left
      show (if Nat.beq t' T = true then Check.triggered else Check.none) = Check.triggered
      rw [ht, if_pos (Nat.beq_refl T)]
    | star =>
      right
      exact ⟨by rw [h0], rfl⟩

/-- A sink check never raises a request on a concrete-mark initial fact. -/
theorem check_request_star {i s : PFact} {f : AFact} {t : Mark} :
    check i f s = .request t → i.mark = .star := by
  intro h
  unfold check at h
  split at h
  · exact Check.noConfusion h
  · split at h
    · split at h
      · split at h
        · exact Check.noConfusion h
        · exact Check.noConfusion h
      · split at h
        · split at h
          · exact Check.noConfusion h
          · exact Check.noConfusion h
        · assumption
    · exact Check.noConfusion h

end ApSpec

/-! ## Axiom audit -/

#print axioms ApSpec.den_covers_final
#print axioms ApSpec.startFact_sound
#print axioms ApSpec.startFact_mark
#print axioms ApSpec.limitF_sound
#print axioms ApSpec.applyEdge_sound
#print axioms ApSpec.applyEdge_reqs_of_star
#print axioms ApSpec.applyEdge_mark_conc
#print axioms ApSpec.applyEdge_reqs_of_conc
#print axioms ApSpec.applySummary_sound
#print axioms ApSpec.applySummary_mark_conc
#print axioms ApSpec.limitF_mark
#print axioms ApSpec.transfer_sound
#print axioms ApSpec.transfer_mark_conc
#print axioms ApSpec.transfer_reqs_of_conc
#print axioms ApSpec.coversB_sound
#print axioms ApSpec.applicable_sound
#print axioms ApSpec.applicable_mark
#print axioms ApSpec.overlapB_of_common
#print axioms ApSpec.answerInit_covers
#print axioms ApSpec.policy_applicable
#print axioms ApSpec.answerInit_applicable
#print axioms ApSpec.answerInit_mark
#print axioms ApSpec.check_sound
#print axioms ApSpec.check_request_star
