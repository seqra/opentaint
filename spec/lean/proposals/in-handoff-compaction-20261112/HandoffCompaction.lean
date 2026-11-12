import Std

/- Handoff guidance only. An arm is a complete canonical paired-output key,
   not an executable OR alternative of an ND rule. Header codes must be bound
   injectively to full owners, ports, marks and protection memberships.
   Request-language coverage is deliberately separate from native C2/C5
   service coverage. In particular the MAY case needs a native progress bridge. -/
namespace HandoffCompaction
set_option autoImplicit false

inductive Tail where | exact | star | may
  deriving DecidableEq, Repr
inductive Need where
  | data (path : List Nat) (tail : Tail)
  | control (key : Nat)
  deriving DecidableEq, Repr
inductive Point where
  | data (path : List Nat)
  | control (key : Nat)
  deriving DecidableEq, Repr

def allows : Need → Point → Prop
  | .data path .exact, .data p => p = path
  | .data path .star, .data p => p = path
  | .data path .may, .data p => ∃ suffix, p = path ++ suffix
  | .control key, .control k => k = key
  | _, _ => False
def covers (broad precise : Need) : Prop :=
  ∀ p, allows precise p → allows broad p

inductive NeedWitness where
  | same
  | point
  | below (suffix : List Nat)
  deriving Repr

def pointTail : Tail → Bool
  | .exact | .star => true
  | .may => false

def checkNeed (broad precise : Need) : NeedWitness → Bool
  | .same => decide (broad = precise)
  | .point => match broad, precise with
    | .data a ta, .data b tb => decide (a = b) && pointTail ta && pointTail tb
    | _, _ => false
  | .below suffix => match broad, precise with
    | .data a .may, .data b _ => decide (b = a ++ suffix)
    | _, _ => false

theorem covers_refl (n : Need) : covers n n := fun _ h => h
theorem covers_trans (a b c : Need) (ab : covers a b) (bc : covers b c) :
    covers a c := fun p h => ab p (bc p h)

theorem below_covers (a suffix : List Nat) (tail : Tail) :
    covers (.data a .may) (.data (a ++ suffix) tail) := by
  intro p h
  cases p with
  | control _ => cases tail <;> exact False.elim h
  | data path =>
    cases tail with
    | exact => exact ⟨suffix, h⟩
    | star => exact ⟨suffix, h⟩
    | may =>
      obtain ⟨rest, eq⟩ := h
      exact ⟨suffix ++ rest, by simpa [List.append_assoc] using eq⟩

theorem checked_need_sound (broad precise : Need) (w : NeedWitness)
    (h : checkNeed broad precise w = true) : covers broad precise := by
  cases w with
  | same =>
    have eq : broad = precise := of_decide_eq_true h
    subst precise
    exact covers_refl broad
  | point =>
    cases broad with
    | control _ => simp [checkNeed] at h
    | data a ta =>
      cases precise with
      | control _ => simp [checkNeed] at h
      | data b tb =>
        have checked : a = b ∧ pointTail ta = true ∧ pointTail tb = true := by
          simpa [checkNeed, Bool.and_eq_true, and_assoc] using h
        have eq := checked.1
        subst b
        cases ta <;> cases tb <;> simp_all [pointTail] <;>
          intro p hp <;> cases p <;> exact hp
  | below suffix =>
    cases broad with
    | control _ => simp [checkNeed] at h
    | data a ta =>
      cases precise with
      | control _ => cases ta <;> simp [checkNeed] at h
      | data b tb =>
        cases ta with
        | exact => simp [checkNeed] at h
        | star => simp [checkNeed] at h
        | may =>
          have eq : b = a ++ suffix := of_decide_eq_true h
          subst b
          exact below_covers a suffix tb

structure Edge where
  header : Nat
  arms : List Nat
  need : Need
  deriving DecidableEq, Repr
structure Token where
  header : Nat
  arm : Nat
  point : Point
  deriving DecidableEq, Repr

def serves (e : Edge) (t : Token) : Prop :=
  e.header = t.header ∧ t.arm ∈ e.arms ∧ allows e.need t.point
def supplied (edges : List Edge) (t : Token) : Prop :=
  ∃ e, e ∈ edges ∧ serves e t

structure ArmWitness where
  arm : Nat
  provider : Edge
  need : NeedWitness
  deriving Repr

def checkWitness (kept : List Edge) (source : Edge) (w : ArmWitness) : Bool :=
  decide (w.provider ∈ kept) && decide (w.provider.header = source.header) &&
  decide (w.arm ∈ w.provider.arms) && checkNeed w.provider.need source.need w.need

def checkEdge (kept : List Edge) (source : Edge) (ws : List ArmWitness) : Bool :=
  !source.arms.isEmpty && source.arms.all (fun arm =>
    ws.any (fun w => decide (w.arm = arm) && checkWitness kept source w))

theorem checked_witness_sound (kept : List Edge) (source : Edge) (w : ArmWitness)
    (h : checkWitness kept source w = true) :
    w.provider ∈ kept ∧ w.provider.header = source.header ∧
    w.arm ∈ w.provider.arms ∧ covers w.provider.need source.need := by
  simp only [checkWitness, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, checked_need_sound _ _ _ h.2⟩

theorem checked_edge_sound (kept : List Edge) (source : Edge) (ws : List ArmWitness)
    (h : checkEdge kept source ws = true) :
    ∀ t, serves source t → supplied kept t := by
  intro t ht
  have all := (Bool.and_eq_true_iff.mp h).2
  have found := List.all_eq_true.mp all t.arm ht.2.1
  obtain ⟨w, _, hw⟩ := List.any_eq_true.mp found
  have eq : w.arm = t.arm := of_decide_eq_true (Bool.and_eq_true_iff.mp hw).1
  obtain ⟨mem, head, arm, need⟩ := checked_witness_sound kept source w
    (Bool.and_eq_true_iff.mp hw).2
  exact ⟨w.provider, mem, head.trans ht.1, eq ▸ arm, need t.point ht.2.2⟩

/- Providers are literal final-retained values. A removed intermediate edge
   is never accepted as a final witness. Rebinding certificates can exploit
   transitivity without retaining an intermediate relation. -/
def checkPlan (original kept : List Edge) (cert : Edge → List ArmWitness) : Bool :=
  kept.all (fun e => decide (e ∈ original)) && original.all (fun e =>
    decide (e ∈ kept) || checkEdge kept e (cert e))

theorem checked_plan_preserves_requests (original kept : List Edge)
    (cert : Edge → List ArmWitness) (h : checkPlan original kept cert = true) :
    ∀ t, supplied original t ↔ supplied kept t := by
  have parts := Bool.and_eq_true_iff.mp h
  intro t
  constructor
  · rintro ⟨e, mem, servesE⟩
    have choice := List.all_eq_true.mp parts.2 e mem
    have alternatives : decide (e ∈ kept) = true ∨ checkEdge kept e (cert e) = true :=
      by simpa only [Bool.or_eq_true] using choice
    rcases alternatives with retained | checked
    · exact ⟨e, of_decide_eq_true retained, servesE⟩
    · exact checked_edge_sound kept e (cert e) checked t servesE
  · rintro ⟨e, mem, servesE⟩
    exact ⟨e, of_decide_eq_true (List.all_eq_true.mp parts.1 e mem), servesE⟩

/- The exact-service bridge abstracts the ALREADY PROVED C2/C5 query checker.
   Each service includes its entire answer/support profile, not just one fact.
   No assumption about MAY progress is hidden in this theorem. -/
def atService {Row Reply : Type} (rows : List Row) (reply : Row → Reply → Prop)
    (answer : Reply) : Prop := ∃ r, r ∈ rows ∧ reply r answer

theorem retained_service_cover {Row Reply : Type} (original kept : List Row)
    (reply : Row → Reply → Prop)
    (subset : ∀ r, r ∈ kept → r ∈ original)
    (cover : ∀ r, r ∈ original → ∀ a, reply r a →
      ∃ provider, provider ∈ kept ∧ reply provider a) :
    ∀ a, atService original reply a ↔ atService kept reply a := by
  intro a
  constructor
  · rintro ⟨r, mem, hr⟩
    exact cover r mem a hr
  · rintro ⟨r, mem, hr⟩
    exact ⟨r, subset r mem, hr⟩

theorem eventual_from_per_step_equality (before after : Nat → Nat → Prop)
    (same : ∀ run sink, before run sink ↔ after run sink) (sink : Nat) :
    (∃ run, before run sink) ↔ (∃ run, after run sink) := by
  constructor
  · rintro ⟨run, found⟩; exact ⟨run, (same run sink).mp found⟩
  · rintro ⟨run, found⟩; exact ⟨run, (same run sink).mpr found⟩

def nd : Edge := ⟨7, [11,12], .data [2] .exact⟩
def first : Edge := ⟨7, [11], .data [2] .exact⟩
def second : Edge := ⟨7, [12], .data [2] .star⟩
def ndCert (_ : Edge) : List ArmWitness :=
  [⟨11,first,.same⟩, ⟨12,second,.point⟩]

theorem nd_two_arms_check : checkPlan [nd,first,second] [first,second] ndCert = true := by
  decide
theorem nd_two_arms_cover : ∀ t,
    supplied [nd,first,second] t ↔ supplied [first,second] t :=
  checked_plan_preserves_requests _ _ _ nd_two_arms_check
theorem nd_missing_arm_rejected : checkEdge [first] nd (ndCert nd) = false := by decide
theorem mutual_deletion_rejected : checkPlan [first,second] [] ndCert = false := by decide
theorem wrong_header_rejected :
    checkWitness [first] {nd with header := 8} ⟨11,first,.same⟩ = false := by decide
theorem other_arrival_order_check :
    checkPlan [second,nd,first] [first,second] ndCert = true := by decide

def mayFirst : Edge := ⟨7, [11], .data [] .may⟩
def mayCert (_ : Edge) : List ArmWitness :=
  [⟨11,mayFirst,.below [2]⟩, ⟨12,second,.point⟩]
theorem may_semantic_plan_check :
    checkPlan [nd,mayFirst,second] [mayFirst,second] mayCert = true := by decide

/- This accepted semantic plan is NOT a proof of native eventual findings.
   The existing first-field emitter is non-extensional in this language. -/
theorem ancestor_star_does_not_cover_child :
    ¬ covers (.data [] .star) (.data [2] .exact) := by
  intro h
  have impossible := h (.data [2]) rfl
  simp [allows] at impossible

#print axioms covers_refl
#print axioms covers_trans
#print axioms below_covers
#print axioms checked_need_sound
#print axioms checked_witness_sound
#print axioms checked_edge_sound
#print axioms checked_plan_preserves_requests
#print axioms retained_service_cover
#print axioms eventual_from_per_step_equality
#print axioms nd_two_arms_check
#print axioms nd_two_arms_cover
#print axioms nd_missing_arm_rejected
#print axioms mutual_deletion_rejected
#print axioms wrong_header_rejected
#print axioms other_arrival_order_check
#print axioms may_semantic_plan_check
#print axioms ancestor_star_does_not_cover_child
end HandoffCompaction
