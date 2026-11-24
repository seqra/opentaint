/-!
# An EXACT cleaner does not apply to a MUST leaf (acyclic proposal §5.5)

Standalone constructive model for `spec/acyclic-group-a-implementation.md` §4.
Lean 4.36.0, core library only, no `Classical`, no `sorry`, no custom axiom.

Scope of the model: one base, one concrete mark that the cleaner selects (the
production `gone(marks)` is not empty), the any-marks of one TAINT leaf. The
production tree walk (`ap/Clean.kt` `TaintClean.cut`) and the reference
(`ap/Reference.kt` `cleanPos`, `concPart`) are both modelled.
-/
namespace MustExactCleaner

/-- Constructive `LawfulBEq Nat` (the library instance goes through `Classical`). -/
local instance (priority := high) natReflBEq : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
local instance (priority := high) natLawfulBEq : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

inductive Tail where
  | exact | star | may | must
deriving DecidableEq, Repr

inductive Reach where
  | exact | below | atAndBelow
deriving DecidableEq, Repr

inductive Layer where
  | normal | demand
deriving DecidableEq, Repr

abbrev Path := List Nat

/-- One TAINT leaf for one mark: path, tail, exclusion (first accessors below the
    path) and layer. -/
structure Leaf where
  path  : Path
  tail  : Tail
  excl  : List Nat
  layer : Layer
deriving DecidableEq, Repr

structure Cleaner where
  path  : Path
  reach : Reach
deriving DecidableEq, Repr

/-- `ExclusionSet.admits`: the first accessor of the rest is not excluded. -/
def admits (e : List Nat) : Path → Bool
  | [] => true
  | a :: _ => !e.contains a

/-- The region `R(λ)` of a leaf (acyclic proposal §2). -/
def inRegion (l : Leaf) (x : Path) : Bool :=
  match l.tail with
  | .exact => x == l.path
  | _ => l.path.isPrefixOf x && admits l.excl (x.drop l.path.length)

inductive CPos where
  | inside | disjoint | part
deriving DecidableEq, Repr

/-- Reference `cleanPos` (`ap/Reference.kt`), base equal. -/
def cleanPos (cl : Cleaner) (c : Leaf) : CPos :=
  if cl.path.length < c.path.length && cl.path.isPrefixOf c.path then
    (if cl.reach == .exact then .disjoint else .inside)
  else if c.path == cl.path then
    (if cl.reach == .atAndBelow then .inside
     else if c.tail == .exact then (if cl.reach == .exact then .inside else .disjoint)
     else .part)
  else if c.path.isPrefixOf cl.path then
    (if c.tail == .exact then .disjoint
     else if admits c.excl (cl.path.drop c.path.length) then .part else .disjoint)
  else .disjoint

/-- Tree form `cleanPosAt` (`ap/Clean.kt`): a leaf on the cleaner spine at depth `d`. -/
def cleanPosAt (cl : Cleaner) (tail : Tail) (d : Nat) (admitsRest : Bool) : CPos :=
  if d < cl.path.length then
    (if tail == .exact then .disjoint else if admitsRest then .part else .disjoint)
  else if tail == .exact then (if cl.reach == .below then .disjoint else .inside)
  else (if cl.reach == .atAndBelow then .inside else .part)

/-- Native PART result for a selected concrete mark (`concPart`; the production
    `cut` branches are the same rows). `marked`: the cleaner names a mark. -/
def nativePart (cl : Cleaner) (marked : Bool) (c : Leaf) : List Leaf :=
  if c.tail == .must && cl.path.length == c.path.length + 1 && c.path.isPrefixOf cl.path
      && cl.reach != .exact then
    let kept : Leaf := { c with excl := cl.path.getLastD 0 :: c.excl }
    if cl.reach == .atAndBelow then [kept]
    else [kept, { path := cl.path, tail := .exact, excl := [], layer := c.layer }]
  else if c.tail != .exact && cl.reach == .below && c.path == cl.path then
    [{ c with tail := .exact, excl := [] }]
  else if c.tail == .star && marked then
    [{ c with tail := .may, excl := [], layer := .demand }]
  else [{ c with layer := .demand }]

/-- The rule: an EXACT cleaner leaves a MUST leaf unchanged at PART. -/
def rulePart (cl : Cleaner) (marked : Bool) (c : Leaf) : List Leaf :=
  if cl.reach == .exact && c.tail == .must then [c] else nativePart cl marked c

/-- The cleaner on one leaf for its selected mark. -/
def cleanOne (part : Cleaner → Bool → Leaf → List Leaf) (cl : Cleaner) (marked : Bool)
    (c : Leaf) : List Leaf :=
  match cleanPos cl c with
  | .disjoint => [c]
  | .inside => []
  | .part => part cl marked c

/-! ## C1-C8: the rule is a layer change of one native row -/

/-- C1. Native: an EXACT cleaner at PART demotes the whole MUST leaf to DEMAND
    (the "survivor"; same path, tail and exclusion). -/
theorem native_exact_must_demotes (cl : Cleaner) (m : Bool) (c : Leaf)
    (hr : cl.reach = .exact) (ht : c.tail = .must) :
    nativePart cl m c = [{ c with layer := .demand }] := by
  unfold nativePart; rw [ht, hr]; simp only [bne_self_eq_false, Bool.and_false]; rfl

/-- C2. The rule keeps the leaf: same path, tail, exclusion and layer. -/
theorem rule_exact_must_keeps (cl : Cleaner) (m : Bool) (c : Leaf)
    (hr : cl.reach = .exact) (ht : c.tail = .must) :
    rulePart cl m c = [c] := by
  unfold rulePart; rw [hr, ht]; rfl

theorem scope_false (cl : Cleaner) (c : Leaf) (h : ¬ (cl.reach = .exact ∧ c.tail = .must)) :
    (cl.reach == .exact && c.tail == .must) = false := by
  cases hr : cl.reach <;> cases ht : c.tail <;> first | rfl | exact absurd ⟨hr, ht⟩ h

/-- C3. Outside its scope the rule is the native row. -/
theorem rule_outside_scope (cl : Cleaner) (m : Bool) (c : Leaf)
    (h : ¬ (cl.reach = .exact ∧ c.tail = .must)) :
    rulePart cl m c = nativePart cl m c := by
  unfold rulePart; rw [scope_false cl c h]; rfl

/-- C4. In its scope, the native rows are the rule rows with the layer set to
    DEMAND. -/
theorem native_is_rule_with_demand_layer (cl : Cleaner) (m : Bool) (c : Leaf)
    (hr : cl.reach = .exact) (ht : c.tail = .must) :
    nativePart cl m c = (rulePart cl m c).map (fun l => { l with layer := .demand }) := by
  rw [native_exact_must_demotes cl m c hr ht, rule_exact_must_keeps cl m c hr ht]
  rfl

/-- C5. The rule changes no position: the regions of the rule rows and of the
    native rows are the same, for every leaf and cleaner. Only a layer changes. -/
theorem same_positions (cl : Cleaner) (m : Bool) (c : Leaf) (x : Path) :
    (rulePart cl m c).any (inRegion · x) = (nativePart cl m c).any (inRegion · x) := by
  by_cases h : cl.reach = .exact ∧ c.tail = .must
  · rw [native_exact_must_demotes cl m c h.1 h.2, rule_exact_must_keeps cl m c h.1 h.2]
    rfl
  · rw [rule_outside_scope cl m c h]

/-- C6. The rule never changes the layer of its input: no DEMAND row from a NORMAL
    input, no NORMAL row from a DEMAND input. -/
theorem rule_keeps_layer (cl : Cleaner) (m : Bool) (c : Leaf)
    (hr : cl.reach = .exact) (ht : c.tail = .must) :
    ∀ l ∈ rulePart cl m c, l.layer = c.layer := by
  rw [rule_exact_must_keeps cl m c hr ht]
  intro l hl
  cases hl with
  | head => rfl
  | tail _ h => cases h

/-- C7. On a DEMAND input the rule and native give the same row. -/
theorem demand_input_unchanged (cl : Cleaner) (m : Bool) (c : Leaf)
    (hd : c.layer = .demand) : rulePart cl m c = nativePart cl m c := by
  by_cases h : cl.reach = .exact ∧ c.tail = .must
  · rw [native_exact_must_demotes cl m c h.1 h.2, rule_exact_must_keeps cl m c h.1 h.2]
    cases c with
    | mk p t e l => dsimp only at hd; subst hd; rfl
  · exact rule_outside_scope cl m c h

/-- C8. The whole cleaner changes only at PART, for an EXACT cleaner, a MUST leaf
    and a NORMAL input. -/
theorem change_only_in_scope (cl : Cleaner) (m : Bool) (c : Leaf)
    (h : cleanOne rulePart cl m c ≠ cleanOne nativePart cl m c) :
    cleanPos cl c = .part ∧ cl.reach = .exact ∧ c.tail = .must ∧ c.layer = .normal := by
  unfold cleanOne at h
  cases hp : cleanPos cl c with
  | disjoint => rw [hp] at h; exact absurd rfl h
  | inside => rw [hp] at h; exact absurd rfl h
  | part =>
    rw [hp] at h
    by_cases hs : cl.reach = .exact ∧ c.tail = .must
    · refine ⟨rfl, hs.1, hs.2, ?_⟩
      cases hl : c.layer
      · rfl
      · exact absurd (demand_input_unchanged cl m c hl) h
    · exact absurd (rule_outside_scope cl m c hs) h

/-! ## C9: the hook in the tree walk has the scope of the reference hook -/

theorem isPrefixOf_take (d : Nat) (p : Path) : (p.take d).isPrefixOf p = true :=
  List.isPrefixOf_iff_prefix.mpr (List.take_prefix d p)

/-- C9. For a leaf on the cleaner spine (`q = p.take d`, `d ≤ |p|`), the tree
    position equals the reference position. The production hook (in `cut`, at
    `Pos.PART`) and the reference hook (in `concPart`, reached only at PART) so
    act on the same leaves. -/
theorem tree_form_is_reference (cl : Cleaner) (c : Leaf) (d : Nat)
    (hd : d ≤ cl.path.length) (hq : c.path = cl.path.take d) :
    cleanPosAt cl c.tail d (admits c.excl (cl.path.drop d)) = cleanPos cl c := by
  have hlen : c.path.length = d := by rw [hq, List.length_take]; omega
  have hpre : c.path.isPrefixOf cl.path = true := by rw [hq]; exact isPrefixOf_take d cl.path
  unfold cleanPosAt cleanPos
  rw [hlen]
  by_cases hlt : d < cl.path.length
  · have hne : (c.path == cl.path) = false := by
      apply beq_false_of_ne; intro e; rw [e] at hlen; omega
    have hnl : decide (cl.path.length < d) = false := decide_eq_false (by omega)
    rw [ite_eq_left_of_eq_true _ _ (eq_true hlt), hnl, Bool.false_and, hne, hpre]
    rfl
  · have hd' : d = cl.path.length := by omega
    have heq : (c.path == cl.path) = true := by
      rw [hq, hd', List.take_length]; exact beq_self_eq_true _
    have hdrop : cl.path.drop d = [] := by rw [hd']; exact List.drop_length
    have hnl : decide (cl.path.length < d) = false := decide_eq_false (by omega)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hlt), hnl, Bool.false_and, heq, hdrop]
    cases c.tail <;> cases cl.reach <;> rfl

/-! ## C10: why native must demote (no finite NORMAL form of the rest) -/

def fresh (xs : List Nat) : Nat := xs.foldr max 0 + 1

theorem lt_fresh {x : Nat} : ∀ {xs : List Nat}, x ∈ xs → x < fresh xs
  | y :: ys, h => by
    unfold fresh
    rw [List.foldr_cons]
    cases h with
    | head => exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
    | tail _ h' =>
      have := lt_fresh (xs := ys) h'
      unfold fresh at this
      exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt_succ this) (Nat.le_max_right _ _))

theorem drop_snoc_head (e : List Nat) (p : Path) (a n : Nat) (hn : n < p.length) :
    admits e ((p ++ [a]).drop n) = admits e (p.drop n) := by
  rw [List.drop_append_of_le_length (Nat.le_of_lt hn)]
  cases h : p.drop n with
  | nil => have := List.drop_eq_nil_iff.mp h; omega
  | cons x r => rfl

theorem prefix_of_snoc {s p : Path} {a : Nat} (h : s <+: p ++ [a]) : s <+: p ∨ s = p ++ [a] := by
  by_cases hl : s.length ≤ p.length
  · exact Or.inl (List.prefix_of_prefix_length_le h (List.prefix_append p [a]) hl)
  · right; apply List.IsPrefix.eq_of_length h
    have h1 := h.length_le
    rw [List.length_append] at h1 ⊢
    exact Nat.le_antisymm h1 (Nat.lt_of_not_le hl)

theorem admits_nil (e : List Nat) : admits e [] = true := rfl

theorem anyRegion (l : Leaf) (ht : l.tail ≠ .exact) (x : Path) :
    inRegion l x = (l.path.isPrefixOf x && admits l.excl (x.drop l.path.length)) := by
  unfold inRegion
  cases h : l.tail
  · exact absurd h ht
  all_goals rfl

theorem own_position (l : Leaf) (ht : l.tail ≠ .exact) : inRegion l l.path = true := by
  rw [anyRegion l ht, List.drop_length, admits_nil, Bool.and_true]
  exact List.isPrefixOf_iff_prefix.mpr (List.prefix_refl _)

/-- C10. Let `c` be a MUST (any-tail) leaf whose region holds the cleaned point
    `p`. A finite set `S` of leaves (any tail, first-accessor exclusions) that does
    not hold `p` misses a strict descendant of `p` in the region of `c`. The
    witness is executable (`fresh`). So the native remainder "the region of `c`
    without the point `p`" has no finite leaf form; native keeps the region whole
    on DEMAND, and the rule keeps it whole on its layer. -/
theorem no_finite_form_without_point (c : Leaf) (hc : c.tail ≠ .exact) (p : Path)
    (hp : inRegion c p = true) (S : List Leaf) (hS : ∀ s ∈ S, inRegion s p = false) :
    ∃ a, inRegion c (p ++ [a]) = true ∧ ∀ s ∈ S, inRegion s (p ++ [a]) = false := by
  let a := fresh (c.excl ++ S.flatMap (·.path))
  refine ⟨a, ?_, ?_⟩
  · rw [anyRegion c hc] at hp ⊢
    have hp' := Bool.and_eq_true_iff.mp hp
    have hpre : c.path <+: p := List.isPrefixOf_iff_prefix.mp hp'.1
    have hpre' : c.path.isPrefixOf (p ++ [a]) = true :=
      List.isPrefixOf_iff_prefix.mpr (hpre.trans (List.prefix_append _ _))
    rw [hpre', Bool.true_and]
    by_cases hl : c.path.length < p.length
    · rw [drop_snoc_head _ _ _ _ hl]; exact hp'.2
    · have heq : c.path = p := hpre.eq_of_length (Nat.le_antisymm hpre.length_le (Nat.le_of_not_lt hl))
      rw [heq, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
      show (!c.excl.contains a) = true
      cases hm : c.excl.contains a
      · rfl
      · have hm' := List.contains_iff_mem.mp hm
        have := lt_fresh (xs := c.excl ++ S.flatMap (·.path)) (List.mem_append_left _ hm')
        exact absurd this (Nat.lt_irrefl _)
  · intro s hs
    have hsp := hS s hs
    have hnotin : ¬ (p ++ [a] = s.path) := by
      intro e
      have hmem : a ∈ s.path := by rw [← e]; exact List.mem_append_right _ (List.mem_singleton_self a)
      have := lt_fresh (xs := c.excl ++ S.flatMap (·.path))
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs, hmem⟩))
      exact absurd this (Nat.lt_irrefl _)
    cases ht : s.tail
    · unfold inRegion; rw [ht]; exact beq_false_of_ne hnotin
    all_goals
      have hne : s.tail ≠ .exact := by rw [ht]; intro e; cases e
      rw [anyRegion s hne]
      cases hin : (s.path.isPrefixOf (p ++ [a]) && admits s.excl ((p ++ [a]).drop s.path.length))
      · rfl
      · have hin' := Bool.and_eq_true_iff.mp hin
        have hpre := List.isPrefixOf_iff_prefix.mp hin'.1
        rcases prefix_of_snoc hpre with hp' | he
        · by_cases hl : s.path.length < p.length
          · have had := hin'.2
            rw [drop_snoc_head _ _ _ _ hl] at had
            have : inRegion s p = true := by
              rw [anyRegion s hne, List.isPrefixOf_iff_prefix.mpr hp', had]; rfl
            rw [this] at hsp; exact absurd hsp (fun e => Bool.noConfusion e)
          · have heq : s.path = p := hp'.eq_of_length (Nat.le_antisymm hp'.length_le (Nat.le_of_not_lt hl))
            have : inRegion s p = true := by rw [← heq]; exact own_position s hne
            rw [this] at hsp; exact absurd hsp (fun e => Bool.noConfusion e)
        · exact absurd he.symm hnotin

/-! ## Example: OWASP `Thing2#doSomething` (reduction) -/

/-- `ret.MUST/T` on NORMAL; the `toString` propagator resets `T` at `ret` with
    reach EXACT. Native gives the DEMAND survivor; the rule keeps the NORMAL leaf. -/
def thing2Ret : Leaf := { path := [], tail := .must, excl := [], layer := .normal }
def thing2Cleaner : Cleaner := { path := [], reach := .exact }

theorem thing2_native : cleanOne nativePart thing2Cleaner true thing2Ret =
    [{ thing2Ret with layer := .demand }] := by decide
theorem thing2_rule : cleanOne rulePart thing2Cleaner true thing2Ret = [thing2Ret] := by decide

end MustExactCleaner

#print axioms MustExactCleaner.native_exact_must_demotes
#print axioms MustExactCleaner.rule_exact_must_keeps
#print axioms MustExactCleaner.rule_outside_scope
#print axioms MustExactCleaner.native_is_rule_with_demand_layer
#print axioms MustExactCleaner.same_positions
#print axioms MustExactCleaner.rule_keeps_layer
#print axioms MustExactCleaner.demand_input_unchanged
#print axioms MustExactCleaner.change_only_in_scope
#print axioms MustExactCleaner.tree_form_is_reference
#print axioms MustExactCleaner.no_finite_form_without_point
#print axioms MustExactCleaner.thing2_native
#print axioms MustExactCleaner.thing2_rule
