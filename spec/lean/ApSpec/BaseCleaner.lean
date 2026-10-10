/-
  F75 local base-relevant selected-mark cleaner.

  This module does not change ApSpec.cleanRes or an analysis closure. Forward
  and backward traces can use this same operation. An abstract mark on the
  cleaner's base always excludes its selected mark and raises its request.
  Path overlap and reach do not decide this abstract case. Concrete marks,
  other bases, and all-mark cleaners retain the current primitive operation.

  The AP operation reports requests. Only RC answers them. FC and BC have no
  request rules; BC follows concrete requirements supplied by the forward
  demand hand-off. This file does not migrate those analysis closures.

  Local exactness means that every normal output pair is an input pair that
  the cleaner preserves. It does not mean that the abstract branch alone
  covers the selected mark: the explicit request supplies that branch.
  No global iteration or coverage theorem is claimed here.
-/
import ApSpec.Exact
import ApSpec.Core

namespace ApSpec.BaseCleaner
open ApSpec

-- Select the constructive Nat reflexivity proof. The generic Ord-derived
-- ReflBEq instance in the library depends on classical order proofs.
local instance : ReflBEq Nat := ⟨by intro n; exact decide_eq_true rfl⟩

/-- The F75 operation. A relevant base means equal fact/cleaner base. -/
def cleanRes (cl : Cleaner) (c : AFact) : Res :=
  match cl.mark, c.fact.mark with
  | some t, .star =>
    if c.fact.base == cl.base then
      ⟨[⟨⟨c.fact.base, c.fact.path, c.fact.kind, addEx c.fact.mark t⟩, c.demand⟩], [t]⟩
    else ApSpec.cleanRes cl c
  | some t, .starEx _ =>
    if c.fact.base == cl.base then
      ⟨[⟨⟨c.fact.base, c.fact.path, c.fact.kind, addEx c.fact.mark t⟩, c.demand⟩], [t]⟩
    else ApSpec.cleanRes cl c
  | _, _ => ApSpec.cleanRes cl c

/-- The one abstract residual, with the input path and layer preserved. -/
def residual (c : AFact) (t : Mark) : AFact :=
  ⟨⟨c.fact.base, c.fact.path, c.fact.kind, addEx c.fact.mark t⟩, c.demand⟩

/-- Equal bases are sufficient; this equation has no path-overlap premise. -/
theorem abstract_same_base {cl : Cleaner} {c : AFact} {t : Mark}
    (hm : Exact.absB c.fact.mark = true) (hb : c.fact.base = cl.base)
    (ht : cl.mark = some t) :
    cleanRes cl c = ⟨[residual c t], [t]⟩ := by
  cases hmark : c.fact.mark with
  | conc m => simp [hmark, Exact.absB] at hm
  | star => simp [cleanRes, ht, hmark, hb, residual]
  | starEx xs => simp [cleanRes, ht, hmark, hb, residual]

/-- Every same-base abstract invocation emits its selected request. -/
theorem abstract_request {cl : Cleaner} {c : AFact} {t : Mark}
    (hm : Exact.absB c.fact.mark = true) (hb : c.fact.base = cl.base)
    (ht : cl.mark = some t) :
    (cleanRes cl c).reqs = [t] := by
  rw [abstract_same_base hm hb ht]

theorem concrete_unchanged {cl : Cleaner} {c : AFact} {m : Mark}
    (hm : c.fact.mark = .conc m) : cleanRes cl c = ApSpec.cleanRes cl c := by
  simp only [cleanRes, hm]
  cases cl.mark <;> rfl

theorem all_marks_unchanged {cl : Cleaner} {c : AFact} (ht : cl.mark = none) :
    cleanRes cl c = ApSpec.cleanRes cl c := by
  simp only [cleanRes, ht]

theorem other_base_unchanged {cl : Cleaner} {c : AFact}
    (hb : c.fact.base ≠ cl.base) : cleanRes cl c = ⟨[c], []⟩ := by
  have hbool : (c.fact.base == cl.base) = false := by
    simp [hb]
  have hold : ApSpec.cleanRes cl c = ⟨[c], []⟩ := by
    simp [ApSpec.cleanRes, cleanPos, hb]
  cases ht : cl.mark <;> cases hm : c.fact.mark <;> simp [cleanRes, ht, hm, hbool, hold]

/-- The root zero fact is concrete. The new abstract override cannot act on it. -/
theorem zero_unchanged (cl : Cleaner) (d : Bool) :
    cleanRes cl ⟨zeroFact, d⟩ = ApSpec.cleanRes cl ⟨zeroFact, d⟩ :=
  concrete_unchanged rfl

/-- A result uses either the new abstract residual or an old primitive result. -/
theorem result_cases {cl : Cleaner} {c r : AFact}
    (hr : r ∈ (cleanRes cl c).facts) :
    (∃ t, Exact.absB c.fact.mark = true ∧ c.fact.base = cl.base ∧
      cl.mark = some t ∧ r = residual c t) ∨
    r ∈ (ApSpec.cleanRes cl c).facts := by
  cases ht : cl.mark with
  | none => exact Or.inr (by simpa [cleanRes, ht] using hr)
  | some t =>
    cases hm : c.fact.mark with
    | conc m => exact Or.inr (by simpa [cleanRes, ht, hm] using hr)
    | star =>
      by_cases hb : c.fact.base = cl.base
      · have he : r = residual c t := by simpa [cleanRes, ht, hm, hb, residual] using hr
        exact Or.inl ⟨t, rfl, hb, rfl, he⟩
      · exact Or.inr (by simpa [cleanRes, ht, hm, hb] using hr)
    | starEx xs =>
      by_cases hb : c.fact.base = cl.base
      · have he : r = residual c t := by simpa [cleanRes, ht, hm, hb, residual] using hr
        exact Or.inl ⟨t, rfl, hb, rfl, he⟩
      · exact Or.inr (by simpa [cleanRes, ht, hm, hb] using hr)

/-- Exact relation of the residual: it removes T everywhere in this abstract
    fact, including locations outside the cleaner's spatial reach. -/
theorem residual_den_iff {i : PFact} {c : AFact} {t : Mark} {l0 l : Loc}
    (hm : Exact.absB c.fact.mark = true) :
    den i (residual c t).fact l0 l ↔
    den i c.fact l0 l ∧ Nat.beq l.mark t = false := by
  constructor
  · exact Exact.addEx_den hm
  · intro ⟨hd, hn⟩
    have he : l.mark = l0.mark := by
      have ho := hd.2.2.2.1
      cases hmark : c.fact.mark with
      | conc m => simp [hmark, Exact.absB] at hm
      | star => simpa [hmark, MarkA.out] using ho
      | starEx xs => simpa [hmark, MarkA.out] using ho
    exact den_addEx hd (by simpa [← he] using hn)

/-- A normal candidate result denotes only concrete flows preserved by the
    cleaner. The extra request does not weaken record exactness. -/
theorem cleanRes_exact {cl : Cleaner} {c r : AFact} {i : PFact} {l0 l : Loc}
    (hr : r ∈ (cleanRes cl c).facts) (hra : r.demand = false)
    (hd : den i r.fact l0 l) : den i c.fact l0 l ∧ cl.cleansB l = false := by
  rcases result_cases hr with ⟨t, hm, _, ht, rfl⟩ | hold
  · obtain ⟨hd', hn⟩ := (residual_den_iff hm).mp hd
    refine ⟨hd', Exact.cleansB_mark ?_⟩
    rw [Exact.markB_some ht]
    exact hn
  · exact Exact.cleanRes_exact hold hra hd

theorem normal_input {cl : Cleaner} {c r : AFact}
    (hr : r ∈ (cleanRes cl c).facts) (hra : r.demand = false) : c.demand = false := by
  rcases result_cases hr with ⟨_, _, _, _, rfl⟩ | hold
  · exact hra
  · exact Exact.cleanRes_demand hold hra

/-- The abstract residual preserves both the path shape and its layer. -/
theorem residual_shape (c : AFact) (t : Mark) :
    (residual c t).fact.base = c.fact.base ∧
    (residual c t).fact.path = c.fact.path ∧
    (residual c t).fact.kind = c.fact.kind ∧
    (residual c t).demand = c.demand := ⟨rfl, rfl, rfl, rfl⟩

theorem operation_cases (cl : Cleaner) (c : AFact) :
    (∃ t, Exact.absB c.fact.mark = true ∧ c.fact.base = cl.base ∧
      cl.mark = some t ∧ cleanRes cl c = ⟨[residual c t], [t]⟩) ∨
    cleanRes cl c = ApSpec.cleanRes cl c := by
  cases ht : cl.mark with
  | none => exact .inr (all_marks_unchanged ht)
  | some t =>
    cases hm : c.fact.mark with
    | conc m => exact .inr (concrete_unchanged hm)
    | star =>
      by_cases hb : c.fact.base = cl.base
      · exact .inl ⟨t, rfl, hb, rfl, abstract_same_base (by rw [hm]; rfl) hb ht⟩
      · exact .inr (by simp [cleanRes, ht, hm, hb])
    | starEx xs =>
      by_cases hb : c.fact.base = cl.base
      · exact .inl ⟨t, rfl, hb, rfl, abstract_same_base (by rw [hm]; rfl) hb ht⟩
      · exact .inr (by simp [cleanRes, ht, hm, hb])

theorem abstract_not_concrete {m : MarkA} (hm : Exact.absB m = true) :
    ∀ t, m ≠ .conc t := by
  intro t ht
  rw [ht] at hm
  cases hm

/-- Every preserved concrete pair has a result or an explicit request. -/
theorem cleanRes_sound {cl : Cleaner} {i : PFact} {c : AFact} {l0 l : Loc}
    (hd : den i c.fact l0 l) (hcl : cl.cleansB l = false) :
    (∃ r, r ∈ (cleanRes cl c).facts ∧ den i r.fact l0 l) ∨
    ((∀ t, c.fact.mark ≠ .conc t) ∧ l0.mark ∈ (cleanRes cl c).reqs) := by
  rcases operation_cases cl c with ⟨t, hm, _, _, he⟩ | he
  · cases hn : Nat.beq l0.mark t with
    | true =>
      refine .inr ⟨abstract_not_concrete hm, ?_⟩
      rw [he]
      exact List.mem_singleton.mpr (CoreAux.beq_iff.mp hn)
    | false =>
      refine .inl ⟨residual c t, ?_, den_addEx hd hn⟩
      rw [he]
      exact List.mem_singleton.mpr rfl
  · rw [he]
    exact ApSpec.cleanRes_sound hd hcl

private theorem old_facts_short (cl : Cleaner) (c : AFact) :
    (ApSpec.cleanRes cl c).facts.length ≤ 1 := by
  unfold ApSpec.cleanRes
  cases hpos : cleanPos cl c.fact <;> cases hm : c.fact.mark <;> cases ht : cl.mark
  all_goals dsimp only
  all_goals first
    | exact Nat.le_refl 1
    | exact Nat.zero_le 1
    | (split <;> first | exact Nat.le_refl 1 | exact Nat.zero_le 1)

theorem facts_short (cl : Cleaner) (c : AFact) : (cleanRes cl c).facts.length ≤ 1 := by
  rcases operation_cases cl c with ⟨_, _, _, _, he⟩ | he
  · rw [he]; exact Nat.le_refl 1
  · rw [he]; exact old_facts_short cl c

private theorem member_headD {cs : List AFact} {r d : AFact}
    (hr : r ∈ cs) (hlen : cs.length ≤ 1) : cs.headD d = r := by
  cases cs with
  | nil => cases hr
  | cons c cs =>
    cases cs with
    | nil =>
      have he : r = c := by simpa using hr
      exact he.symm
    | cons c' cs => simp at hlen

/-- Data, rather than an existential proof alone: either a selected output
    fact with its pair, or the selected requested input mark. -/
inductive CoverageWitness (cl : Cleaner) (i : PFact) (c : AFact) (l0 l : Loc) : Type where
  | output (r : AFact) (member : r ∈ (cleanRes cl c).facts) (pair : den i r.fact l0 l)
  | request (t : Mark) (same : t = l0.mark) (abstract : ∀ m, c.fact.mark ≠ .conc m)
      (member : t ∈ (cleanRes cl c).reqs)

/-- Executable selection. The output is the finite result's first fact; the
    proof that it covers the pair uses the at-most-one-result invariant. -/
def cleanRes_sound_witness {cl : Cleaner} {i : PFact} {c : AFact} {l0 l : Loc}
    (hd : den i c.fact l0 l) (hcl : cl.cleansB l = false) :
    CoverageWitness cl i c l0 l :=
  if hr : l0.mark ∈ (cleanRes cl c).reqs then
    .request l0.mark rfl (by
      rcases operation_cases cl c with ⟨_, hm, _, _, _⟩ | he
      · exact abstract_not_concrete hm
      · rw [he] at hr
        exact (ApSpec.cleanRes_reqs_abstract hr).1) hr
  else
    .output ((cleanRes cl c).facts.headD c)
      (by
        rcases cleanRes_sound hd hcl with ⟨r, hm, _⟩ | ⟨_, hm⟩
        · rw [member_headD hm (facts_short cl c)]
          exact hm
        · exact False.elim (hr hm))
      (by
        rcases cleanRes_sound hd hcl with ⟨r, hm, hp⟩ | ⟨_, hm⟩
        · rw [member_headD hm (facts_short cl c)]
          exact hp
        · exact False.elim (hr hm))

/-- F75's abstract-mode cleaner gate is based on fact base relevance. Concrete
    preservation, AP-result membership and denotation remain separate premises. -/
def cleanMABBase (cl : Cleaner) (f : AFact) (l : Loc) : Bool :=
  if f.fact.base == cl.base then
    match cl.mark with
    | none => true
    | some t => !(Nat.beq l.mark t)
  else true

theorem abstract_mode_same_base {cl : Cleaner} {f : AFact} {l : Loc} {t : Mark}
    (hb : f.fact.base = cl.base) (ht : cl.mark = some t) :
    cleanMABBase cl f l = !(Nat.beq l.mark t) := by
  simp only [cleanMABBase, hb, ht, beq_self_eq_true, ↓reduceIte]

theorem abstract_mode_other_base {cl : Cleaner} {f : AFact} {l : Loc}
    (hb : f.fact.base ≠ cl.base) : cleanMABBase cl f l = true := by
  simp [cleanMABBase, hb]

theorem abstract_mode_all_marks {cl : Cleaner} {f : AFact} {l : Loc}
    (ht : cl.mark = none) : cleanMABBase cl f l = true := by
  unfold cleanMABBase
  rw [ht]
  split <;> rfl

/-! ## Uniform-base batch: concept and guarded optimization

  The list is a finite denotation of one maintained uniform abstract batch.
  This is not a proof of a trie implementation. The cost counts cleaner base
  guards only; it does not count list allocation, mark re-keying, or mapping
  the leaf payloads. A tree can share a root only under its own representation
  invariant. Nothing in these list theorems supplies that invariant.
-/

/-- The literal per-leaf concept, including duplicate requests. -/
def leafBatch (cl : Cleaner) (cs : List AFact) : Res :=
  ⟨cs.flatMap (fun c => (cleanRes cl c).facts),
   cs.flatMap (fun c => (cleanRes cl c).reqs)⟩

def dedupRequests (r : Res) : Res := ⟨r.facts, r.reqs.eraseDups⟩

/-- The uniform batch invariant is explicit and is erased from execution. -/
structure UniformAbstractBatch where
  base : Base
  facts : List AFact
  uniform : ∀ c, c ∈ facts → c.fact.base = base ∧ Exact.absB c.fact.mark = true

theorem leaf_batch_uniform {cl : Cleaner} {cs : List AFact} {t : Mark}
    (ht : cl.mark = some t)
    (hu : ∀ c, c ∈ cs → c.fact.base = cl.base ∧ Exact.absB c.fact.mark = true) :
    (leafBatch cl cs).facts = cs.map (fun c => residual c t) ∧
    (leafBatch cl cs).reqs = List.replicate cs.length t := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c cs ih =>
    obtain ⟨hb, hm⟩ := hu c (by simp)
    have htail : ∀ d, d ∈ cs → d.fact.base = cl.base ∧ Exact.absB d.fact.mark = true := by
      intro d hd
      exact hu d (by simp [hd])
    obtain ⟨hf, hr⟩ := ih htail
    have hc := abstract_same_base hm hb ht
    constructor
    · simp only [leafBatch, List.flatMap_cons, hc, List.singleton_append, List.map_cons]
      exact congrArg (fun fs => residual c t :: fs) hf
    · simp only [leafBatch, List.flatMap_cons, hc, List.singleton_append, List.length_cons,
        List.replicate_succ]
      exact congrArg (fun rs => t :: rs) hr

private theorem filter_repeated_mark (n : Nat) (t : Mark) :
    (List.replicate n t).filter (fun b => !(b == t)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.filter_cons, beq_self_eq_true, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, ih]

theorem eraseDups_replicate (n : Nat) (t : Mark) :
    (List.replicate n t).eraseDups = if n = 0 then [] else [t] := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [List.replicate_succ, List.eraseDups_cons, filter_repeated_mark]
    rfl

/-- Abstract facts in a nonempty same-base batch all become `*∖T`. The batch
    raises exactly one T request after request-set duplicate removal. -/
theorem batch_uniform_nonempty {cl : Cleaner} {cs : List AFact} {t : Mark}
    (ht : cl.mark = some t)
    (hu : ∀ c, c ∈ cs → c.fact.base = cl.base ∧ Exact.absB c.fact.mark = true)
    (hne : cs ≠ []) :
    dedupRequests (leafBatch cl cs) = ⟨cs.map (fun c => residual c t), [t]⟩ := by
  obtain ⟨hf, hr⟩ := leaf_batch_uniform ht hu
  have hlen : cs.length ≠ 0 := by simpa using hne
  simp only [dedupRequests, hf, hr, eraseDups_replicate, hlen, if_false]

/-- An executable concept walk and its literal count of per-leaf base guards. -/
def leafBatchCount (cl : Cleaner) : List AFact → Res × Nat
  | [] => (⟨[], []⟩, 0)
  | c :: cs =>
    let tail := leafBatchCount cl cs
    (Res.append (cleanRes cl c) tail.1, tail.2 + 1)

theorem leaf_batch_count (cl : Cleaner) (cs : List AFact) :
    (leafBatchCount cl cs).1 = leafBatch cl cs ∧
    (leafBatchCount cl cs).2 = cs.length := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c cs ih =>
    obtain ⟨hv, hn⟩ := ih
    constructor
    · simp only [leafBatchCount, hv, Res.append, leafBatch, List.flatMap_cons]
    · simp only [leafBatchCount, hn, List.length_cons]

/-- One base guard on a maintained uniform abstract batch. It does not scan
    each leaf to check the `uniform` proof. Payload mapping remains explicit. -/
def uniformBatchCount (cl : Cleaner) (batch : UniformAbstractBatch) : Res × Nat :=
  match cl.mark with
  | some t =>
    if batch.base == cl.base then
      (⟨batch.facts.map (fun c => residual c t), if batch.facts.isEmpty then [] else [t]⟩, 1)
    else (⟨batch.facts, []⟩, 1)
  | none =>
    let r := leafBatchCount cl batch.facts
    (dedupRequests r.1, r.2)

/-- Functional equivalence on any nonempty same-base abstract batch. -/
theorem uniform_batch_equiv {cl : Cleaner} {batch : UniformAbstractBatch} {t : Mark}
    (ht : cl.mark = some t) (hb : batch.base = cl.base) (hne : batch.facts ≠ []) :
    (uniformBatchCount cl batch).1 = dedupRequests (leafBatchCount cl batch.facts).1 ∧
    (uniformBatchCount cl batch).2 = 1 ∧
    (leafBatchCount cl batch.facts).2 = batch.facts.length := by
  have hu : ∀ c, c ∈ batch.facts → c.fact.base = cl.base ∧ Exact.absB c.fact.mark = true := by
    intro c hc
    obtain ⟨hcb, hcm⟩ := batch.uniform c hc
    exact ⟨hcb.trans hb, hcm⟩
  have hnorm := batch_uniform_nonempty ht hu hne
  obtain ⟨hvalue, hcount⟩ := leaf_batch_count cl batch.facts
  have hempty : batch.facts.isEmpty = false := by
    cases hf : batch.facts with
    | nil => exact False.elim (hne hf)
    | cons c cs => rfl
  refine ⟨?_, ?_, hcount⟩
  · simp [uniformBatchCount, ht, hb, hempty, hvalue, hnorm]
  · simp [uniformBatchCount, ht, hb]

/-! ## Executable review vectors and witnesses -/

def clExact : Cleaner := ⟨4, [], .exact, some 1⟩
def clWhole : Cleaner := ⟨4, [], .atAndBelow, some 1⟩
def clBelow : Cleaner := ⟨4, [], .below, some 1⟩
def clField : Cleaner := ⟨4, [7], .atAndBelow, some 1⟩
def clOther : Cleaner := ⟨8, [], .atAndBelow, some 1⟩
def clAll : Cleaner := ⟨4, [], .atAndBelow, none⟩
def rootStar : AFact := ⟨⟨4, [], .star .empty, .star⟩, false⟩
def fieldStar : AFact := ⟨⟨4, [4], .star .empty, .star⟩, false⟩
def fieldEx : AFact := ⟨⟨4, [4], .star (.set [7]), .starEx [2]⟩, false⟩
def excludedT : AFact := ⟨⟨4, [4], .star .empty, .starEx [1]⟩, false⟩
def rootT : AFact := ⟨⟨4, [], .exact, .conc 1⟩, false⟩
def fieldT : AFact := ⟨⟨4, [4], .exact, .conc 1⟩, false⟩
def rootOtherT : AFact := ⟨⟨4, [], .exact, .conc 2⟩, false⟩
def demandStar : AFact := ⟨⟨4, [4], .any, .star⟩, true⟩

structure CleanerVector where
  label : String
  cleaner : Cleaner
  input : AFact
  facts : List AFact
  reqs : List Mark

def vectors : List CleanerVector := [
  ⟨"root EXACT, spatially disjoint field", clExact, fieldStar,
    [⟨⟨4, [4], .star .empty, .starEx [1]⟩, false⟩], [1]⟩,
  ⟨"whole-base abstract fact", clWhole, rootStar,
    [⟨⟨4, [], .star .empty, .starEx [1]⟩, false⟩], [1]⟩,
  ⟨"partial root EXACT abstract fact", clExact, rootStar,
    [⟨⟨4, [], .star .empty, .starEx [1]⟩, false⟩], [1]⟩,
  ⟨"partial child cleaner abstract fact", clField, rootStar,
    [⟨⟨4, [], .star .empty, .starEx [1]⟩, false⟩], [1]⟩,
  ⟨"apart field paths on the same base", clField, fieldStar,
    [⟨⟨4, [4], .star .empty, .starEx [1]⟩, false⟩], [1]⟩,
  ⟨"same-base root exact tail, below-only reach", clBelow, ⟨⟨4, [], .exact, .star⟩, false⟩,
    [⟨⟨4, [], .exact, .starEx [1]⟩, false⟩], [1]⟩,
  ⟨"other base abstract fact", clOther, fieldStar, [fieldStar], []⟩,
  ⟨"abstract mark with another exclusion", clExact, fieldEx,
    [⟨⟨4, [4], .star (.set [7]), .starEx [1, 2]⟩, false⟩], [1]⟩,
  ⟨"T already excluded still requests T", clExact, excludedT,
    [⟨⟨4, [4], .star .empty, .starEx [1, 1]⟩, false⟩], [1]⟩,
  ⟨"demand input keeps its path and layer", clExact, demandStar,
    [⟨⟨4, [4], .any, .starEx [1]⟩, true⟩], [1]⟩,
  ⟨"concrete cleaned root", clExact, rootT, [], []⟩,
  ⟨"concrete disjoint field", clExact, fieldT, [fieldT], []⟩,
  ⟨"concrete other selected mark", clWhole, rootOtherT, [rootOtherT], []⟩,
  ⟨"concrete partly cleaned fact", clExact, ⟨⟨4, [], .star .empty, .conc 1⟩, false⟩,
    [⟨⟨4, [], .star .empty, .conc 1⟩, true⟩], []⟩,
  ⟨"all-mark cleaner unchanged", clAll, rootStar, [], []⟩,
  ⟨"zero fact unchanged on an ordinary base", clExact, ⟨zeroFact, false⟩,
    [⟨zeroFact, false⟩], []⟩
]

def vectorOK (v : CleanerVector) : Bool :=
  let r := cleanRes v.cleaner v.input
  decide (r.facts = v.facts ∧ r.reqs = v.reqs)

theorem vectors_pass : vectors.all vectorOK = true := by decide

/-- This executable pair shows why same-base spatial disjointness now needs
    a request: the residual excludes T, while its concrete answer survives. -/
def requestedDisjointWitness :
    { c : AFact //
      c = fieldStar ∧
      cleanPos clExact c.fact = .disjoint ∧
      1 ∈ (cleanRes clExact c).reqs ∧
      den ⟨3, [], .star .empty, .star⟩ c.fact ⟨3, [], 1⟩ ⟨4, [4], 1⟩ ∧
      ¬den ⟨3, [], .star .empty, .star⟩ (residual c 1).fact ⟨3, [], 1⟩ ⟨4, [4], 1⟩ ∧
      (cleanRes clExact fieldT).facts = [fieldT] } :=
  by
    refine ⟨fieldStar, rfl, by decide, by decide, ?_, ?_, by decide⟩
    · exact ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, ⟨rfl, rfl⟩⟩
    · intro hd
      have hn := ((residual_den_iff (c := fieldStar) rfl).mp hd).2
      cases hn

def CoverageWitness.value {cl : Cleaner} {i : PFact} {c : AFact} {l0 l : Loc} :
    CoverageWitness cl i c l0 l → Option AFact × Option Mark
  | .output r _ _ => (some r, none)
  | .request t _ _ _ => (none, some t)

def requestedPair (m : Mark) :
    CoverageWitness clExact ⟨3, [], .star .empty, .star⟩ fieldStar
      ⟨3, [], m⟩ ⟨4, [4], m⟩ :=
  cleanRes_sound_witness
    ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, ⟨rfl, rfl⟩⟩
    (by simp [Cleaner.cleansB, clExact, Cleaner.markB, CleanReach.inB, dropPrefix])

theorem coverage_selection :
    (requestedPair 1).value = (none, some 1) ∧
    (requestedPair 2).value = (some (residual fieldStar 1), none) := by decide

theorem mode_vectors :
    cleanMABBase clExact fieldStar ⟨4, [4], 1⟩ = false ∧
    cleanMABBase clExact fieldStar ⟨4, [4], 2⟩ = true ∧
    cleanMABBase clOther fieldStar ⟨4, [4], 1⟩ = true ∧
    cleanMABBase clAll fieldStar ⟨4, [4], 1⟩ = true := by decide

def workBatch : UniformAbstractBatch :=
  ⟨4, (List.range 33).map (fun n => ⟨⟨4, [n + 4], .star .empty, .star⟩, false⟩), by
    intro c hc
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hc
    exact ⟨rfl, rfl⟩⟩

theorem work_batch_distinct_paths : (workBatch.facts.map (fun c => c.fact.path)).Nodup := by decide

/-- Practical finite witness: equal batch values after request deduplication,
    with 33 base guards for the concept and one guard for the uniform batch. -/
def workWitness :
    { counts : Nat × Nat //
      counts = ((leafBatchCount clExact workBatch.facts).2,
        (uniformBatchCount clExact workBatch).2) ∧
      counts = (33, 1) ∧
      (uniformBatchCount clExact workBatch).1 =
        dedupRequests (leafBatchCount clExact workBatch.facts).1 } :=
  ⟨(33, 1), by decide, rfl,
    (uniform_batch_equiv (cl := clExact) (batch := workBatch) rfl rfl (by decide)).1⟩

#eval vectors.map (fun v => (v.label, vectorOK v))
#eval workWitness.val
#eval [(requestedPair 1).value, (requestedPair 2).value]
#print axioms cleanRes_exact
#print axioms cleanRes_sound
#print axioms cleanRes_sound_witness
#print axioms batch_uniform_nonempty
#print axioms uniform_batch_equiv
#print axioms requestedDisjointWitness
#print axioms workWitness

end ApSpec.BaseCleaner

