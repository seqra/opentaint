import Std

namespace ProgramDedup

/-- Ordinary payload identity is opaque; protection is a finite independent mask. -/
structure Packet (bits : Nat) where
  payload : Nat
  protection : Fin bits → Bool

abbrev State (bits : Nat) := List (Packet bits)

def maskLe {bits : Nat} (a b : Fin bits → Bool) : Prop :=
  ∀ bit, a bit = true → b bit = true

def maskOr {bits : Nat} (a b : Fin bits → Bool) : Fin bits → Bool := fun bit => a bit || b bit

theorem mask_le_or_left {bits : Nat} (a b : Fin bits → Bool) : maskLe a (maskOr a b) := by
  intro bit present
  simp [maskOr, present]

theorem mask_le_or_right {bits : Nat} (a b : Fin bits → Bool) : maskLe b (maskOr a b) := by
  intro bit present
  simp [maskOr, present]

theorem mask_le_trans {bits : Nat} {a b c : Fin bits → Bool}
    (ab : maskLe a b) (bc : maskLe b c) : maskLe a c := fun bit present => bc bit (ab bit present)

theorem mask_or_covered {bits : Nat} (old incoming : Fin bits → Bool)
    (covered : maskLe incoming old) : maskOr old incoming = old := by
  funext bit
  change (old bit || incoming bit) = old bit
  cases a : old bit <;> cases b : incoming bit
  · rfl
  · have contradiction := covered bit b
    rw [a] at contradiction
    cases contradiction
  · rfl
  · rfl

def mergePacket {bits : Nat} (old incoming : Packet bits) : Packet bits :=
  ⟨old.payload, maskOr old.protection incoming.protection⟩

/-- Ordered union: first occurrence owns its position; equal payloads OR protection. -/
def add {bits : Nat} (incoming : Packet bits) : State bits → State bits
  | [] => [incoming]
  | old :: rest => if incoming.payload = old.payload then mergePacket old incoming :: rest
                   else old :: add incoming rest

def covers {bits : Nat} (packet : Packet bits) : State bits → Prop
  | [] => False
  | old :: rest => if packet.payload = old.payload then maskLe packet.protection old.protection
                   else covers packet rest

theorem add_of_covered {bits : Nat} (packet : Packet bits) (state : State bits)
    (covered : covers packet state) : add packet state = state := by
  induction state with
  | nil => exact False.elim covered
  | cons old rest ih =>
    by_cases same : packet.payload = old.payload
    · simp only [covers, if_pos same] at covered
      have merged : mergePacket old packet = old := by
        cases old
        simp only [mergePacket]
        rw [mask_or_covered _ _ covered]
      simp [add, same, merged]
    · simp only [covers, if_neg same] at covered
      simp [add, same, ih covered]

theorem covers_after_add_self {bits : Nat} (packet : Packet bits) (state : State bits) :
    covers packet (add packet state) := by
  induction state with
  | nil => simp [add, covers, maskLe]
  | cons old rest ih =>
    by_cases same : packet.payload = old.payload
    · simp only [add, covers, mergePacket, if_pos same]
      exact mask_le_or_right _ _
    · simpa only [add, if_neg same, covers, if_neg same] using ih

theorem covers_preserved_by_add {bits : Nat} (packet incoming : Packet bits) (state : State bits)
    (covered : covers packet state) : covers packet (add incoming state) := by
  induction state with
  | nil => exact False.elim covered
  | cons old rest ih =>
    by_cases packetSame : packet.payload = old.payload
    · simp only [covers, if_pos packetSame] at covered
      by_cases incomingSame : incoming.payload = old.payload
      · simp only [add, if_pos incomingSame, covers, mergePacket, if_pos packetSame]
        exact mask_le_trans covered (mask_le_or_left _ _)
      · simpa only [add, if_neg incomingSame, covers, if_pos packetSame] using covered
    · simp only [covers, if_neg packetSame] at covered
      by_cases incomingSame : incoming.payload = old.payload
      · simpa only [add, if_pos incomingSame, covers, mergePacket, if_neg packetSame] using covered
      · simpa only [add, if_neg incomingSame, covers, if_neg packetSame] using ih covered

def runPackets {bits : Nat} (state : State bits) : List (Packet bits) → State bits
  | [] => state
  | packet :: rest => runPackets (add packet state) rest

theorem run_preserves_coverage {bits : Nat} (packet : Packet bits) (state : State bits)
    (stream : List (Packet bits)) (covered : covers packet state) :
    covers packet (runPackets state stream) := by
  induction stream generalizing state with
  | nil => exact covered
  | cons incoming rest ih =>
    exact ih _ (covers_preserved_by_add packet incoming state covered)

theorem run_covers_every_packet {bits : Nat} (state : State bits) (stream : List (Packet bits))
    (packet : Packet bits) (member : packet ∈ stream) : covers packet (runPackets state stream) := by
  induction stream generalizing state with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst packet
      exact run_preserves_coverage head (add head state) rest (covers_after_add_self head state)
    · exact ih (add head state) later

theorem run_covered_stream_is_identity {bits : Nat} (state : State bits) (stream : List (Packet bits))
    (covered : ∀ packet ∈ stream, covers packet state) : runPackets state stream = state := by
  induction stream with
  | nil => rfl
  | cons packet rest ih =>
    simp only [runPackets, add_of_covered packet state (covered packet List.mem_cons_self)]
    exact ih (fun other member => covered other (List.mem_cons_of_mem packet member))

theorem identical_stream_is_idempotent {bits : Nat} (state : State bits) (stream : List (Packet bits)) :
    runPackets (runPackets state stream) stream = runPackets state stream := by
  exact run_covered_stream_is_identity _ stream
    (fun packet member => run_covers_every_packet state stream packet member)

variable {Program : Type} [DecidableEq Program]

def nativePrograms {bits : Nat} (emit : Program → List (Packet bits)) (state : State bits) :
    List Program → State bits
  | [] => state
  | program :: rest => nativePrograms emit (runPackets state (emit program)) rest

def stablePrograms (seen : List Program) : List Program → List Program
  | [] => []
  | program :: rest => if program ∈ seen then stablePrograms seen rest
                        else program :: stablePrograms (program :: seen) rest

def dedupPrograms {bits : Nat} (emit : Program → List (Packet bits))
    (seen : List Program) (state : State bits) : List Program → State bits
  | [] => state
  | program :: rest => if program ∈ seen then dedupPrograms emit seen state rest
                        else dedupPrograms emit (program :: seen) (runPackets state (emit program)) rest

theorem stable_program_count_bound (programs : List Program) (seen : List Program) :
    (stablePrograms seen programs).length ≤ programs.length := by
  induction programs generalizing seen with
  | nil => exact Nat.le_refl 0
  | cons program rest ih =>
    by_cases repeated : program ∈ seen
    · simp only [stablePrograms, if_pos repeated, List.length_cons]
      exact Nat.le_trans (ih seen) (Nat.le_succ _)
    · simpa only [stablePrograms, if_neg repeated, List.length_cons] using Nat.add_le_add_right (ih (program :: seen)) 1

theorem dedup_programs_equal_native_stable {bits : Nat} (emit : Program → List (Packet bits))
    (programs : List Program) (seen : List Program) (state : State bits) :
    dedupPrograms emit seen state programs = nativePrograms emit state (stablePrograms seen programs) := by
  induction programs generalizing seen state with
  | nil => rfl
  | cons program rest ih =>
    by_cases repeated : program ∈ seen <;> simp [dedupPrograms, stablePrograms, repeated, nativePrograms, ih]

theorem stable_dedup_preserves_ordered_union {bits : Nat} (emit : Program → List (Packet bits))
    (programs : List Program) (seen : List Program) (state : State bits)
    (invariant : ∀ program ∈ seen, ∀ packet ∈ emit program, covers packet state) :
    dedupPrograms emit seen state programs = nativePrograms emit state programs := by
  induction programs generalizing seen state with
  | nil => rfl
  | cons program rest ih =>
    by_cases repeated : program ∈ seen
    · have unchanged := run_covered_stream_is_identity state (emit program) (invariant program repeated)
      simp only [dedupPrograms, if_pos repeated, nativePrograms, unchanged]
      exact ih seen state invariant
    · simp only [dedupPrograms, if_neg repeated, nativePrograms]
      apply ih
      intro prior member packet emitted
      rcases List.mem_cons.mp member with same | earlier
      · subst prior
        exact run_covers_every_packet state (emit program) packet emitted
      · exact run_preserves_coverage packet state (emit program) (invariant prior earlier packet emitted)

def eligiblePrograms {Row : Type} (eligible : Row → Bool) (program : Row → Program) (rows : List Row) : List Program :=
  (rows.filter eligible).map program

theorem after_eligibility_exact_ordered_outputs {bits : Nat} {Row : Type}
    (emit : Program → List (Packet bits)) (eligible : Row → Bool) (program : Row → Program)
    (rows : List Row) (state : State bits) :
    nativePrograms emit state (stablePrograms [] (eligiblePrograms eligible program rows)) =
      nativePrograms emit state (eligiblePrograms eligible program rows) := by
  rw [← dedup_programs_equal_native_stable]
  exact stable_dedup_preserves_ordered_union emit _ [] state (fun _ member => False.elim (List.not_mem_nil member))

def exampleEmit : Nat → List (Packet 2)
  | 0 => [⟨5, fun bit => bit.val == 0⟩, ⟨7, fun _ => false⟩]
  | _ => [⟨5, fun bit => bit.val == 1⟩]

theorem example_exact_first_output_order :
    (nativePrograms exampleEmit [] [0, 1, 0]).map Packet.payload = [5, 7] := rfl

theorem example_protection_upgrade_is_retained :
    ((nativePrograms exampleEmit [] [0, 1, 0]).map (fun packet => packet.protection 0)) = [true, false] ∧
    ((nativePrograms exampleEmit [] [0, 1, 0]).map (fun packet => packet.protection 1)) = [true, false] := by decide

theorem example_repeated_programs_keep_first_order : stablePrograms [] [3, 1, 3, 2, 1] = [3, 1, 2] := rfl

theorem example_fewer_output_program_evaluations : (stablePrograms [] [0, 1, 0]).length = 2 := rfl

theorem dedup_before_eligibility_is_unsound :
    eligiblePrograms (fun (row : Bool × Nat) => row.1) Prod.snd [(false, 0), (true, 0)] = [0] ∧
    eligiblePrograms (fun (row : Bool × Nat) => row.1) Prod.snd [(false, 0)] = [] := by decide

end ProgramDedup
