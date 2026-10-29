import DirectedAlias.Sound.Complete

/-!
# A checkable certificate for the completeness scope

`Safe` (no execution blocks on null) is a semantic condition. This file gives a small
must-analysis that checks it for core programs. Each variable has a kind:
* `sym`: the variable holds a symbolic object (its fields are never null in a core program);
* `obj`: the variable holds some object;
* `maybe`: the variable can be null.
A load is safe if its base is not `maybe`. With it, the scope `coreScopeB` is a Boolean
function, so `decide` can check that a program is in the scope.
-/

namespace DirectedAlias.Sound

open DirectedAlias

/-- The null kind of a variable. -/
inductive NK where
  | sym
  | obj
  | maybe
  deriving DecidableEq, Repr

/-- The join of two null kinds: the weaker fact. -/
def NK.join : NK → NK → NK
  | .sym, .sym => .sym
  | .maybe, _ => .maybe
  | _, .maybe => .maybe
  | _, _ => .obj

/-- The null-kind transfer of a core statement. It fails on a load through a `maybe` base. -/
def nstep (k : Var → NK) : Stmt → Option (Var → NK)
  | .new x _ => some (fupd k x .obj)
  | .null x => some (fupd k x .maybe)
  | .copy x y => some (fupd k x (k y))
  | .load x y _ => if k y = .maybe then none else
      some (fupd k x (if k y = .sym then .sym else .maybe))
  | .aload x y => if k y = .maybe then none else
      some (fupd k x (if k y = .sym then .sym else .maybe))
  | .unknown x _ => some (fupd k x .sym)
  | _ => none

/-- The null-kind analysis of a core program. It fails if a load can block. -/
def nsafe : Prog → (Var → NK) → Option (Var → NK)
  | .skip, k => some k
  | .stmt st, k => nstep k st
  | .seq p q, k => (nsafe p k).bind (nsafe q)
  | .choice p q, k =>
    match nsafe p k, nsafe q k with
    | some k1, some k2 => some (fun x => (k1 x).join (k2 x))
    | _, _ => none
  | .loop _, _ => none

/-- The entry kinds: each frame variable holds a symbolic root object. -/
def entryKinds (fr : Frame) (x : Var) : NK :=
  match fr.root? x with
  | some _ => .sym
  | none => .maybe

/-- The Boolean null-safety check of a program. -/
def nullSafeB (fr : Frame) (p : Prog) : Bool :=
  (nsafe p (entryKinds fr)).isSome

/-- A concrete state agrees with the null kinds. -/
def Good (k : Var → NK) (t : CState) : Prop :=
  ∀ x, (k x = .sym → ∃ b p, t.env x = some (.sym b p)) ∧ (k x ≠ .maybe → ∃ o, t.env x = some o)

/-- `Good` after a variable update. -/
theorem Good.set {k : Var → NK} {t : CState} (h : Good k t) (x : Var) (a : NK) (v : Val)
    (hv1 : a = .sym → ∃ b p, v = some (.sym b p)) (hv2 : a ≠ .maybe → ∃ o, v = some o) :
    Good (fupd k x a) (t.setVar x v) := by
  intro y
  by_cases e : y = x
  · subst e
    show (fupd k y a y = .sym → ∃ b p, fupd t.env y v y = _) ∧
      (fupd k y a y ≠ .maybe → ∃ o, fupd t.env y v y = _)
    simp only [fupd_same]
    exact ⟨hv1, hv2⟩
  · show (fupd k x a y = .sym → ∃ b p, fupd t.env x v y = _) ∧ (fupd k x a y ≠ .maybe → ∃ o, fupd t.env x v y = _)
    rw [fupd_ne _ _ e, fupd_ne _ _ e]
    exact h y

/-- The null-kind check of one statement is sound: the statement can run, and the new kinds
hold after each step. -/
theorem nstep_sound {k k' : Var → NK} {st : Stmt} (h : nstep k st = some k') {t : CState}
    (hg : Good k t) (hh : t.heap = cdefault) :
    (∃ u, SStep st t u) ∧ ∀ u, SStep st t u → Good k' u := by
  cases st with
  | new x s =>
    simp only [nstep, Option.some.injEq] at h; subst h
    refine ⟨⟨_, .new⟩, fun u hu => ?_⟩
    cases hu
    exact Good.set hg x .obj _ (fun e => by cases e) (fun _ => ⟨_, rfl⟩)
  | null x =>
    simp only [nstep, Option.some.injEq] at h; subst h
    refine ⟨⟨_, .null⟩, fun u hu => ?_⟩
    cases hu
    exact Good.set hg x .maybe _ (fun e => by cases e) (fun e => absurd rfl e)
  | copy x y =>
    simp only [nstep, Option.some.injEq] at h; subst h
    refine ⟨⟨_, .copy⟩, fun u hu => ?_⟩
    cases hu
    exact Good.set hg x _ _ (hg y).1 (hg y).2
  | unknown x s =>
    simp only [nstep, Option.some.injEq] at h; subst h
    refine ⟨⟨_, .unknown⟩, fun u hu => ?_⟩
    cases hu
    exact Good.set hg x .sym _ (fun _ => ⟨_, _, rfl⟩) (fun _ => ⟨_, rfl⟩)
  | load x y f =>
    simp only [nstep] at h
    split at h
    · cases h
    · rename_i hy
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨o, ho⟩ := (hg y).2 hy
      refine ⟨⟨_, .load ho⟩, fun u hu => ?_⟩
      cases hu with
      | load ho' =>
        rename_i o'
        rw [ho] at ho'; cases ho'
        refine Good.set hg x _ _ ?_ ?_
        · intro e
          split at e
          · rename_i hs
            obtain ⟨b, p, hp⟩ := (hg y).1 hs
            rw [ho] at hp; cases hp
            rw [hh]; exact ⟨b, _, rfl⟩
          · cases e
        · intro e
          split at e
          · rename_i hs
            obtain ⟨b, p, hp⟩ := (hg y).1 hs
            rw [ho] at hp; cases hp
            rw [hh]; exact ⟨_, rfl⟩
          · exact absurd rfl e
  | aload x y =>
    simp only [nstep] at h
    split at h
    · cases h
    · rename_i hy
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨o, ho⟩ := (hg y).2 hy
      refine ⟨⟨_, .aload 0 ho⟩, fun u hu => ?_⟩
      cases hu with
      | aload i ho' =>
        rename_i o'
        rw [ho] at ho'; cases ho'
        refine Good.set hg x _ _ ?_ ?_
        · intro e
          split at e
          · rename_i hs
            obtain ⟨b, p, hp⟩ := (hg y).1 hs
            rw [ho] at hp; cases hp
            rw [hh]; exact ⟨b, _, rfl⟩
          · cases e
        · intro e
          split at e
          · rename_i hs
            obtain ⟨b, p, hp⟩ := (hg y).1 hs
            rw [ho] at hp; cases hp
            rw [hh]; exact ⟨_, rfl⟩
          · exact absurd rfl e
  | store _ _ _ => simp [nstep] at h
  | astore _ _ => simp [nstep] at h
  | call _ _ _ => simp [nstep] at h

/-- If the join is `sym`, the left kind is `sym`. -/
theorem NK.join_sym_left {a b : NK} (h : a.join b = .sym) : a = .sym := by
  cases a <;> cases b <;> first | rfl | cases h

/-- If the join is `sym`, the right kind is `sym`. -/
theorem NK.join_sym_right {a b : NK} (h : a.join b = .sym) : b = .sym := by
  cases a <;> cases b <;> first | rfl | cases h

/-- If the join is not `maybe`, the left kind is not `maybe`. -/
theorem NK.join_nm_left {a b : NK} (h : a.join b ≠ .maybe) : a ≠ .maybe := by
  cases a <;> cases b <;> first | exact absurd rfl h | (intro e; cases e)

/-- If the join is not `maybe`, the right kind is not `maybe`. -/
theorem NK.join_nm_right {a b : NK} (h : a.join b ≠ .maybe) : b ≠ .maybe := by
  cases a <;> cases b <;> first | exact absurd rfl h | (intro e; cases e)

/-- A state that agrees with the left kinds agrees with the join. -/
theorem Good.joinL {k1 k2 : Var → NK} {t : CState} (h : Good k1 t) :
    Good (fun x => (k1 x).join (k2 x)) t :=
  fun x => ⟨fun e => (h x).1 (NK.join_sym_left e), fun e => (h x).2 (NK.join_nm_left e)⟩

/-- A state that agrees with the right kinds agrees with the join. -/
theorem Good.joinR {k1 k2 : Var → NK} {t : CState} (h : Good k2 t) :
    Good (fun x => (k1 x).join (k2 x)) t :=
  fun x => ⟨fun e => (h x).1 (NK.join_sym_right e), fun e => (h x).2 (NK.join_nm_right e)⟩

/-- The null-kind analysis is sound: a core program that passes the check does not block,
and the final kinds hold after each execution. -/
theorem nsafe_sound : ∀ (q : Prog) {k k' : Var → NK}, coreP q = true → nsafe q k = some k' →
    ∀ {t : CState}, Good k t → t.heap = cdefault → Safe q t ∧ ∀ u, Exec q t u → Good k' u := by
  intro q
  induction q with
  | skip =>
    intro k k' _ h t hg _
    simp only [nsafe, Option.some.injEq] at h; subst h
    exact ⟨trivial, fun u hu => by cases hu; exact hg⟩
  | stmt st =>
    intro k k' _ h t hg hh
    obtain ⟨h1, h2⟩ := nstep_sound h hg hh
    exact ⟨h1, fun u hu => by cases hu with | stmt hs => exact h2 u hs⟩
  | seq p q ihp ihq =>
    intro k k' hc h t hg hh
    simp only [coreP, Bool.and_eq_true] at hc
    simp only [nsafe] at h
    cases e : nsafe p k with
    | none => rw [e] at h; cases h
    | some k1 =>
      rw [e, Option.bind_some] at h
      obtain ⟨hs1, hg1⟩ := ihp hc.1 e hg hh
      refine ⟨⟨hs1, fun u hu => (ihq hc.2 h (hg1 u hu) ((core_heap hu hc.1).trans hh)).1⟩, ?_⟩
      intro v hv
      cases hv with
      | seq h1 h2 =>
        rename_i u
        exact (ihq hc.2 h (hg1 u h1) ((core_heap h1 hc.1).trans hh)).2 v h2
  | choice p q ihp ihq =>
    intro k k' hc h t hg hh
    simp only [coreP, Bool.and_eq_true] at hc
    simp only [nsafe] at h
    cases e1 : nsafe p k with
    | none => rw [e1] at h; cases h
    | some k1 =>
      cases e2 : nsafe q k with
      | none => rw [e1, e2] at h; cases h
      | some k2 =>
        rw [e1, e2] at h
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hs1, hg1⟩ := ihp hc.1 e1 hg hh
        obtain ⟨hs2, hg2⟩ := ihq hc.2 e2 hg hh
        refine ⟨⟨hs1, hs2⟩, fun u hu => ?_⟩
        cases hu with
        | choiceL h1 => exact (hg1 u h1).joinL
        | choiceR h1 => exact (hg2 u h1).joinR
  | loop _ _ => intro k k' _ h; simp [nsafe] at h

/-- The entry state agrees with the entry kinds. -/
theorem good_entry (fr : Frame) : Good (entryKinds fr) (CState.init fr) := by
  intro x
  unfold entryKinds
  cases e : fr.root? x with
  | none => exact ⟨fun h => NK.noConfusion h, fun h => absurd rfl h⟩
  | some r =>
    have hv : (CState.init fr).env x = some (Obj.sym (Base.root r) []) := by
      simp [CState.init, e]
    exact And.intro (fun _ => Exists.intro (Base.root r) (Exists.intro [] hv))
      (fun _ => Exists.intro _ hv)

/-- A core program that passes the null check does not block from the entry state. -/
theorem nullSafe_safe {fr : Frame} {p : Prog} (hc : coreP p = true) (h : nullSafeB fr p = true) :
    Safe p (CState.init fr) := by
  unfold nullSafeB at h
  cases e : nsafe p (entryKinds fr) with
  | none => rw [e] at h; cases h
  | some k' => exact (nsafe_sound p hc e (good_entry fr) rfl).1

/-- The checkable form of the store-free core scope. -/
def coreScopeB (K : Nat) (fr : Frame) (p : Prog) (px py : List ACell) : Bool :=
  coreP p && p.sites.all p.onceB && decide (loadsP p + px.length ≤ K) &&
    decide (loadsP p + py.length ≤ K) && nullSafeB fr p

/-- The checkable scope implies the semantic scope. -/
theorem coreScopeB_sound {K : Nat} {fr : Frame} {p : Prog} {px py : List ACell}
    (h : coreScopeB K fr p px py = true) : CoreScope K fr p px py := by
  simp only [coreScopeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, nullSafe_safe h1 h5⟩

/-- Completeness in the checkable store-free core scope. -/
theorem ccomplete_coreB (K : Nat) :
    CCompleteIn K (fun fr p px py => coreScopeB K fr p px py = true) :=
  fun fr p x px y py hs hm => ccomplete_core K fr p x px y py (coreScopeB_sound hs) hm

end DirectedAlias.Sound
