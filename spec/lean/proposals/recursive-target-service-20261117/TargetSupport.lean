namespace RecursiveTargetSupport
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

inductive Origin where
  | report (id : Nat)
  | unknown
  deriving DecidableEq, BEq, Repr

def confirmed (known : Nat → Bool) : Origin → Bool
  | .report id=>known id
  | .unknown=>false

-- Both relations describe real terminal events, never DATA edges. Unknown
-- emitters are seeds too. A call can relay a terminal without adding a mark.
inductive Derivation (seed : Nat → Origin → Prop) (link : Nat → Nat → Prop) :
    Nat → Origin → Prop
  | source (present : seed v origin) : Derivation seed link v origin
  | relay (present : link child parent) (earlier : Derivation seed link child origin) :
      Derivation seed link parent origin

structure ClosedCertificate (known : Nat → Bool) (seed : Nat → Origin → Prop)
    (link : Nat → Nat → Prop) (needs : Nat → Bool) : Prop where
  seedCase : ∀v origin, seed v origin → confirmed known origin=false → needs v=true
  relay : ∀a b, link a b → needs a=true → needs b=true

theorem every_unconfirmed_origin_sets_the_bit
    (certificate : ClosedCertificate known seed link needs)
    (path : Derivation seed link v origin) (missing : confirmed known origin=false) : needs v=true := by
  induction path with
  | source present=>exact certificate.seedCase _ _ present missing
  | relay present _ ih=>exact certificate.relay _ _ present (ih missing)

theorem a_false_bit_covers_every_finite_origin_even_through_recursion
    (certificate : ClosedCertificate known seed link needs)
    (quiet : needs v=false) (path : Derivation seed link v origin) : confirmed known origin=true := by
  cases status : confirmed known origin
  · have live:=every_unconfirmed_origin_sets_the_bit certificate path status
    rw [quiet] at live
    cases live
  · rfl

theorem unknown_origins_always_keep_the_row
    (certificate : ClosedCertificate known seed link needs)
    (path : Derivation seed link v .unknown) : needs v=true :=
  every_unconfirmed_origin_sets_the_bit certificate path rfl

theorem any_mixed_unconfirmed_origin_prevents_retirement {id : Nat}
    (certificate : ClosedCertificate known seed link needs)
    (path : Derivation seed link v (.report id)) (notYet : known id=false) : needs v=true :=
  every_unconfirmed_origin_sets_the_bit certificate path notYet

-- The regular target row is still emitted. The extra event only upgrades
-- this Boolean at that same key; it does not replay any DATA packet.
def accept (old : Option Bool) (offered : Bool) : Option Bool × Bool :=
  match old with
  | none=>(some offered,true)
  | some previous=>let next:=previous || offered
                   (some next,next != previous)

def events (old : Option Bool) : List Bool → List Bool
  | []=>[]
  | b::rest=>let (next,changed):=accept old b
             (if changed then [next.getD true] else []) ++ events next rest

def budget : Option Bool → Nat
  | none=>2
  | some false=>1
  | some true=>0

theorem at_most_two_target_notifications_per_existing_key
    (old : Option Bool) (offered : List Bool) : (events old offered).length≤budget old := by
  induction offered generalizing old with
  | nil=>exact Nat.zero_le _
  | cons bit rest ih=>
    cases old with
    | none=>
      cases bit with
      | false=>
        change (events (some false) rest).length+1≤2
        exact Nat.succ_le_succ (ih (some false))
      | true=>
        change (events (some true) rest).length+1≤2
        exact Nat.le_trans (Nat.succ_le_succ (ih (some true))) (by decide)
    | some previous=>
      cases previous with
      | false=>
        cases bit with
        | false=>exact ih (some false)
        | true=>exact Nat.succ_le_succ (ih (some true))
      | true=>cases bit <;> exact ih (some true)

theorem a_late_unconfirmed_derivation_upgrades_a_previously_covered_row :
    events none [false,false,true,false,true]=[false,true] := rfl

-- Pure handoff filter. Only forward root ZERO/DT is eligible.
def retire (forward root zero certified : Bool) (needs : Bool) : Bool :=
  forward && root && zero && certified && !needs

theorem nonroot_backward_nonzero_and_uncertified_rows_are_unchanged :
    retire false root zero certified needs=false ∧
    retire forward false zero certified needs=false ∧
    retire forward root false certified needs=false ∧
    retire forward root zero false needs=false := by
  repeat constructor <;> simp [retire]

theorem a_needed_row_cannot_be_dropped : retire forward root zero certified true=false := by
  simp [retire]

theorem a_retired_root_row_cannot_contain_an_unconfirmed_observation
    (certificate : ClosedCertificate known seed link needs)
    (removed : retire true true true true (needs v)=true)
    (path : Derivation seed link v origin) : confirmed known origin=true := by
  have quiet : needs v=false := by
    cases bit : needs v <;> simp_all [retire]
  exact a_false_bit_covers_every_finite_origin_even_through_recursion certificate quiet path

-- No current ID, field suffix, call history or origin set is stored on an
-- AP fact. The stable snapshot is existing confirmed root report IDs.
theorem empty_snapshot_never_covers_a_report (id : Nat) :
    confirmed (fun _=>false) (.report id)=false := rfl

theorem confirmation_membership_is_not_a_LOCAL_conditional_normal_target
    (known : Nat → Bool) (id : Nat) (rootConfirmed : known id=false) :
    confirmed known (.report id)=false := rootConfirmed

def fullOriginNeeds (known : Nat → Bool) (origins : List Origin) : Bool:=
  origins.any (fun origin=> !confirmed known origin)

theorem one_bit_union_equals_the_conceptual_origin_union
    (known : Nat → Bool) (left right : List Origin) :
    fullOriginNeeds known (left++right)=
      (fullOriginNeeds known left || fullOriginNeeds known right) := by
  exact List.any_append

theorem duplicate_origin_proofs_do_not_change_the_bit
    (known : Nat → Bool) (origin : Origin) :
    fullOriginNeeds known [origin,origin]=fullOriginNeeds known [origin] := by
  simp [fullOriginNeeds]

-- Executable finite oracle for tests. Production can establish the same
-- invariant by owner serialization and draining all metadata upgrades.
-- It need not keep a second graph or full origin sets to run this check.
def validate (known : Nat → Bool) (seeds : List (Nat × Origin))
    (links : List (Nat × Nat)) (needs : Nat → Bool) : Bool:=
  seeds.all (fun (v,o)=>confirmed known o || needs v) &&
  links.all (fun (a,b)=> !needs a || needs b)

theorem the_finite_validator_constructs_the_closed_certificate
    (known : Nat → Bool) (seeds : List (Nat × Origin)) (links : List (Nat × Nat))
    (needs : Nat → Bool) (passed : validate known seeds links needs=true) :
    ClosedCertificate known (fun v o=>(v,o)∈seeds) (fun a b=>(a,b)∈links) needs := by
  have halves:=Bool.and_eq_true_iff.mp passed
  constructor
  · intro v origin present missing
    have checked:=(List.all_eq_true.mp halves.1) (v,origin) present
    simpa only [missing,Bool.false_or] using checked
  · intro a b present live
    have checked:=(List.all_eq_true.mp halves.2) (a,b) present
    simpa only [live,Bool.not_true,Bool.false_or] using checked

end RecursiveTargetSupport
