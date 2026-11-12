import Std

/- Exact FULL mark relations at one fixed complete geometry/header key.
   Nat encodes an opaque full-mark identity, not a group or JVM type.
   Lists model finite sets; native MarkSet/maps must bind their membership.
   The diagonal and changing parts never imply a Cartesian product. -/
namespace CallerMarkRelations
set_option autoImplicit false

abbrev MarkPair := Nat × Nat
structure Packed where
  diagonal : List Nat
  changing : List MarkPair
  deriving DecidableEq, Repr

def empty : Packed := ⟨[],[]⟩
def insert {α : Type} [DecidableEq α] (item : α) (items : List α) : List α :=
  if item ∈ items then items else item :: items

theorem mem_insert {α : Type} [DecidableEq α] (item query : α) (items : List α) :
    query ∈ insert item items ↔ query = item ∨ query ∈ items := by
  by_cases h : item ∈ items
  · simp only [insert, ite_eq_left h]
    constructor
    · exact Or.inr
    · rintro (eq | mem)
      · exact eq ▸ h
      · exact mem
  · simp [insert,h]

theorem insert_idempotent {α : Type} [DecidableEq α] (item : α) (items : List α) :
    insert item (insert item items) = insert item items := by
  by_cases h : item ∈ items <;> simp [insert,h]

def decode (packed : Packed) : List MarkPair :=
  packed.diagonal.map (fun mark => (mark,mark)) ++ packed.changing

theorem decoded_membership (packed : Packed) (pair : MarkPair) :
    pair ∈ decode packed ↔
      (pair.1 = pair.2 ∧ pair.1 ∈ packed.diagonal) ∨ pair ∈ packed.changing := by
  constructor
  · intro h
    rcases List.mem_append.mp h with diag | cross
    · obtain ⟨mark,mem,eq⟩ := List.mem_map.mp diag
      subst pair
      exact Or.inl ⟨rfl,mem⟩
    · exact Or.inr cross
  · rintro (⟨same,mem⟩ | cross)
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨pair.1,mem,Prod.ext rfl same⟩
    · exact List.mem_append_right _ cross

def put (packed : Packed) (pair : MarkPair) : Packed :=
  if pair.1 = pair.2 then
    {packed with diagonal := insert pair.1 packed.diagonal}
  else {packed with changing := insert pair packed.changing}

theorem put_exact_membership (packed : Packed) (offered query : MarkPair) :
    query ∈ decode (put packed offered) ↔ query = offered ∨ query ∈ decode packed := by
  by_cases same : offered.1 = offered.2
  · have shape : query ∈ decode (put packed offered) ↔
        (query.1 = query.2 ∧ (query.1 = offered.1 ∨ query.1 ∈ packed.diagonal)) ∨
          query ∈ packed.changing := by
      rw [decoded_membership]
      simp only [put,ite_eq_left same,mem_insert]
    rw [shape]
    constructor
    · rintro (⟨eq,first | old⟩ | old)
      · exact Or.inl (Prod.ext first (eq.symm.trans (first.trans same)))
      · exact Or.inr ((decoded_membership packed query).mpr (Or.inl ⟨eq,old⟩))
      · exact Or.inr ((decoded_membership packed query).mpr (Or.inr old))
    · rintro (eq | old)
      · subst query
        exact Or.inl ⟨same,Or.inl rfl⟩
      · rcases (decoded_membership packed query).mp old with ⟨eq,diag⟩ | cross
        · exact Or.inl ⟨eq,Or.inr diag⟩
        · exact Or.inr cross
  · rw [decoded_membership]
    simp only [put,ite_eq_right same,mem_insert]
    constructor
    · rintro (diag | eq | cross)
      · exact Or.inr ((decoded_membership packed query).mpr (Or.inl diag))
      · exact Or.inl eq
      · exact Or.inr ((decoded_membership packed query).mpr (Or.inr cross))
    · rintro (eq | old)
      · exact Or.inr (Or.inl eq)
      · rcases (decoded_membership packed query).mp old with diag | cross
        · exact Or.inl diag
        · exact Or.inr (Or.inr cross)

def canonical (packed : Packed) : Prop :=
  ∀ pair, pair ∈ packed.changing → pair.1 ≠ pair.2
theorem empty_canonical : canonical empty := by
  intro pair mem
  simp [empty] at mem
theorem put_canonical (packed : Packed) (pair : MarkPair) (h : canonical packed) :
    canonical (put packed pair) := by
  intro query mem
  by_cases same : pair.1 = pair.2
  · exact h query (by simpa [put,same] using mem)
  · have member : query ∈ insert pair packed.changing := by simpa [put,same] using mem
    rcases (mem_insert pair query packed.changing).mp member with eq | old
    · exact eq ▸ same
    · exact h query old

def putAll (packed : Packed) (offered : List MarkPair) : Packed :=
  offered.foldl put packed

theorem put_all_exact (packed : Packed) (offered : List MarkPair) (query : MarkPair) :
    query ∈ decode (putAll packed offered) ↔ query ∈ offered ∨ query ∈ decode packed := by
  induction offered generalizing packed with
  | nil => simp [putAll]
  | cons pair rest ih =>
    change query ∈ decode (putAll (put packed pair) rest) ↔ _
    rw [ih,put_exact_membership]
    simp only [List.mem_cons]
    constructor
    · rintro (tail | eq | old)
      · exact Or.inl (Or.inr tail)
      · exact Or.inl (Or.inl eq)
      · exact Or.inr old
    · rintro ((eq | tail) | old)
      · exact Or.inr (Or.inl eq)
      · exact Or.inl tail
      · exact Or.inr (Or.inr old)

def encode (pairs : List MarkPair) : Packed := putAll empty pairs
theorem exact_decode_encode (pairs : List MarkPair) (query : MarkPair) :
    query ∈ decode (encode pairs) ↔ query ∈ pairs := by
  simpa [encode,decode,empty] using put_all_exact empty pairs query

def fresh (packed : Packed) (offered : List MarkPair) : List MarkPair :=
  offered.filter (fun pair => decide (pair ∉ decode packed))
theorem exact_fresh_delta (packed : Packed) (offered : List MarkPair) (query : MarkPair) :
    query ∈ fresh packed offered ↔ query ∈ offered ∧ query ∉ decode packed := by
  simp [fresh]

theorem duplicate_put_idempotent (packed : Packed) (pair : MarkPair) :
    put (put packed pair) pair = put packed pair := by
  by_cases same : pair.1 = pair.2
  · simp [put,same,insert_idempotent]
  · simp [put,same,insert_idempotent]

theorem arrival_order_membership (packed : Packed) (a b query : MarkPair) :
    query ∈ decode (put (put packed a) b) ↔ query ∈ decode (put (put packed b) a) := by
  simp only [put_exact_membership]
  constructor
  · rintro (hb | ha | old)
    · exact Or.inr (Or.inl hb)
    · exact Or.inl ha
    · exact Or.inr (Or.inr old)
  · rintro (ha | hb | old)
    · exact Or.inr (Or.inl ha)
    · exact Or.inl hb
    · exact Or.inr (Or.inr old)

def targets (packed : Packed) (source : Nat) : List Nat :=
  (decode packed).filterMap (fun pair => if pair.1 = source then some pair.2 else none)

theorem targets_exact (packed : Packed) (source target : Nat) :
    target ∈ targets packed source ↔ (source,target) ∈ decode packed := by
  simp only [targets,List.mem_filterMap]
  constructor
  · rintro ⟨pair,mem,hit⟩
    split at hit
    next eq =>
      have out : pair.2 = target := Option.some.inj hit
      have same : pair = (source,target) := Prod.ext eq out
      exact same ▸ mem
    next => contradiction
  · intro mem
    exact ⟨(source,target),mem,by simp⟩

def sources (packed : Packed) (target : Nat) : List Nat :=
  (decode packed).filterMap (fun pair => if pair.2 = target then some pair.1 else none)
theorem sources_exact (packed : Packed) (source target : Nat) :
    source ∈ sources packed target ↔ (source,target) ∈ decode packed := by
  simp only [sources,List.mem_filterMap]
  constructor
  · rintro ⟨pair,mem,hit⟩
    split at hit
    next eq =>
      have input : pair.1 = source := Option.some.inj hit
      have same : pair = (source,target) := Prod.ext input eq
      exact same ▸ mem
    next => contradiction
  · intro mem
    exact ⟨(source,target),mem,by simp⟩

/- Native changingByTarget is a finite map of target -> source MarkSet.
   Flattening that map has exactly these pair memberships. Map uniqueness
   and MarkSet deduplication refine the list model without adding pairs. -/
def bucketPairs (buckets : List (Nat × List Nat)) : List MarkPair :=
  buckets.flatMap (fun bucket => bucket.2.map (fun source => (source,bucket.1)))
theorem target_bucket_membership (buckets : List (Nat × List Nat)) (source target : Nat) :
    (source,target) ∈ bucketPairs buckets ↔
      ∃ bucket, bucket ∈ buckets ∧ bucket.1 = target ∧ source ∈ bucket.2 := by
  constructor
  · intro h
    obtain ⟨bucket,mem,found⟩ := List.mem_flatMap.mp h
    obtain ⟨input,present,eq⟩ := List.mem_map.mp found
    have fst : input = source := congrArg Prod.fst eq
    have snd : bucket.1 = target := congrArg Prod.snd eq
    exact ⟨bucket,mem,snd,fst ▸ present⟩
  · rintro ⟨bucket,mem,eq,present⟩
    apply List.mem_flatMap.mpr
    exact ⟨bucket,mem,List.mem_map.mpr ⟨source,present,Prod.ext rfl eq⟩⟩

/- For any existing scalar operation, including mark changes and protection
   decisions, the exact same scalar pair is passed to it. No packed transfer
   with a representative source mark is introduced. -/
def replies {Reply : Type} (pairs : List MarkPair) (apply : MarkPair → List Reply) : List Reply :=
  pairs.flatMap apply
theorem arbitrary_scalar_replies {Reply : Type} (pairs : List MarkPair)
    (apply : MarkPair → List Reply) (reply : Reply) :
    reply ∈ replies (decode (encode pairs)) apply ↔ reply ∈ replies pairs apply := by
  simp only [replies,List.mem_flatMap]
  constructor
  · rintro ⟨pair,mem,answer⟩
    exact ⟨pair,(exact_decode_encode pairs pair).mp mem,answer⟩
  · rintro ⟨pair,mem,answer⟩
    exact ⟨pair,(exact_decode_encode pairs pair).mpr mem,answer⟩

/- Geometry/header identity is retained by the outer key. This wrapper shows
   why pair coverage at one key cannot merge ownership or H at another. -/
def atKey (key : Nat) (pairs : List MarkPair) : List (Nat × MarkPair) :=
  pairs.map (fun pair => (key,pair))
theorem different_key_separate (a b : Nat) (pairs : List MarkPair) (query : MarkPair)
    (different : a ≠ b) : (a,query) ∉ atKey b pairs := by
  intro h
  obtain ⟨pair,_,eq⟩ := List.mem_map.mp h
  exact different (congrArg Prod.fst eq).symm

/- Literal geometry coordinates include path and exact/ANY leaf slot.
   The outer family retains the complete native packet header. Splitting
   cells is representation only; replay reconstructs the full packet. -/
abbrev Atom := Nat × Nat
abbrev Cell := Nat × MarkPair
def factorPacket (source : Nat) (atoms : List Atom) : List Cell :=
  atoms.map (fun atom => (atom.1,(source,atom.2)))
def restorePacket (source : Nat) (cells : List Cell) : List Atom :=
  cells.filterMap (fun cell => if cell.2.1 = source then some (cell.1,cell.2.2) else none)

theorem factor_packet_roundtrip (source : Nat) (atoms : List Atom) :
    restorePacket source (factorPacket source atoms) = atoms := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih => simpa [restorePacket,factorPacket] using congrArg (List.cons atom) ih

theorem other_source_packet_empty (source other : Nat) (atoms : List Atom)
    (different : source ≠ other) : restorePacket other (factorPacket source atoms) = [] := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih => simp_all [restorePacket,factorPacket]

theorem restore_packet_union (source : Nat) (left right : List Cell) :
    restorePacket source (left ++ right) = restorePacket source left ++ restorePacket source right := by
  simp [restorePacket,List.filterMap_append]

def sourceCellPostings (source : Nat) (cells : List Cell) : List Nat :=
  cells.filterMap (fun cell => if cell.2.1 = source then some cell.1 else none)

theorem source_cell_postings_exact (source geometry : Nat) (cells : List Cell) :
    geometry ∈ sourceCellPostings source cells ↔
      ∃ target, (geometry,(source,target)) ∈ cells := by
  simp only [sourceCellPostings,List.mem_filterMap]
  constructor
  · rintro ⟨cell,mem,found⟩
    split at found
    next eq =>
      have locationEq : cell.1 = geometry := Option.some.inj found
      have same : cell = (geometry,(source,cell.2.2)) := Prod.ext locationEq (Prod.ext eq rfl)
      exact ⟨cell.2.2,same ▸ mem⟩
    next => contradiction
  · rintro ⟨target,mem⟩
    exact ⟨(geometry,(source,target)),mem,by simp⟩

theorem source_postings_union (source : Nat) (left right : List Cell) :
    sourceCellPostings source (left ++ right) =
      sourceCellPostings source left ++ sourceCellPostings source right := by
  simp [sourceCellPostings,List.filterMap_append]

def showcase : List MarkPair := [(1,1),(3,3),(1,2),(3,4)]
theorem diagonal_mask_example : (encode [(1,1),(3,3)]).changing = [] := by decide
theorem changing_pairs_example : (1,2) ∈ decode (encode showcase) ∧
    (3,4) ∈ decode (encode showcase) := by decide
theorem no_cartesian_product : (1,4) ∉ decode (encode showcase) ∧
    (3,2) ∉ decode (encode showcase) := by decide
theorem same_source_two_targets :
    (1,2) ∈ decode (encode [(1,2),(1,4)]) ∧ (1,4) ∈ decode (encode [(1,2),(1,4)]) := by decide
theorem two_sources_same_target : sources (encode [(1,2),(3,2)]) 2 = [3,1] := by decide

#print axioms mem_insert
#print axioms insert_idempotent
#print axioms decoded_membership
#print axioms put_exact_membership
#print axioms empty_canonical
#print axioms put_canonical
#print axioms put_all_exact
#print axioms exact_decode_encode
#print axioms exact_fresh_delta
#print axioms duplicate_put_idempotent
#print axioms arrival_order_membership
#print axioms targets_exact
#print axioms sources_exact
#print axioms target_bucket_membership
#print axioms arbitrary_scalar_replies
#print axioms different_key_separate
#print axioms factor_packet_roundtrip
#print axioms other_source_packet_empty
#print axioms restore_packet_union
#print axioms source_cell_postings_exact
#print axioms source_postings_union
#print axioms diagonal_mask_example
#print axioms changing_pairs_example
#print axioms no_cartesian_product
#print axioms same_source_two_targets
#print axioms two_sources_same_target
end CallerMarkRelations
