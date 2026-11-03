import Std

namespace PackedStaticGuidance

/- Selected representation design. These finite values are already normalized
   by the old boundary adapter. Geometry metadata remains opaque and exact. -/
inductive Base where
  | zero | static | other (id : Nat)
  deriving DecidableEq, Repr

inductive Tail where
  | exact | star | any | must
  deriving DecidableEq, Repr

structure Endpoint where
  base : Base
  fields : List Nat
  tail : Tail
  fieldExclusions : List Nat
  deriving DecidableEq, Repr

structure Geometry where
  input : Endpoint
  output : Option Endpoint
  deriving DecidableEq, Repr

inductive Label where
  | flow
  | mapped (input output : Nat)
  | terminal (input : Nat)
  deriving DecidableEq, Repr

/- General nullable relation coding has a zero sentinel. The selected boundary
   word uses both actual concrete endpoint IDs, including control ZERO, as id+1.
   Nullable GuidanceMarks are derived from typed endpoint bases, never decoded
   into a runtime ZERO fact. B retains its existing non-null-endpoint codec. -/
def markCode : Option Nat → Nat
  | none => 0
  | some n => n+1

def decodeMarkCode : Nat → Option Nat
  | 0 => none
  | n+1 => some n

theorem mark_code_roundtrip (m : Option Nat) : decodeMarkCode (markCode m) = m := by
  cases m <;> rfl

def pairWord (radix input output : Nat) : Nat := radix * input + output

def decodeWord (radix word : Nat) : Nat × Nat := (word / radix, word % radix)

theorem packed_pair_roundtrip (radix a b : Nat) (hr : 0 < radix) (hb : b < radix) :
    decodeWord radix (pairWord radix a b) = (a,b) := by
  simp [decodeWord, pairWord, Nat.mul_add_div hr,
    Nat.div_eq_of_lt hb, Nat.mod_eq_of_lt hb]

theorem packed_word_bound (radix a b : Nat) (ha : a < radix) (hb : b < radix) :
    pairWord radix a b < radix * radix := by
  have hm := Nat.mul_le_mul_left radix (Nat.add_one_le_iff.mpr ha)
  have ht := Nat.add_lt_add_left hb (radix*a)
  simp only [Nat.mul_add, Nat.mul_one] at hm
  unfold pairWord
  omega

theorem colored_word_not_flow (radix a b : Nat) (hr : 0 < radix) (hb : b < radix)
    (h : a ≠ 0 ∨ b ≠ 0) : pairWord radix a b ≠ 0 := by
  intro hz
  have eq := packed_pair_roundtrip radix a b hr hb
  rw [hz] at eq
  simp only [decodeWord, Nat.zero_div, Nat.zero_mod] at eq
  have ha := congrArg Prod.fst eq
  have hb := congrArg Prod.snd eq
  rcases h with h | h <;> simp_all

inductive Relation where
  | flow
  | mapped (input output : Option Nat)
  | terminal (input : Nat)
  deriving DecidableEq, Repr

inductive Family where
  | writer | reader | bridge | terminal
  deriving DecidableEq, Repr

structure Owner where
  method : Nat
  context : List Nat
  block : Nat
  entry : Int
  exit : Int
  family : Family
  deriving DecidableEq, Repr

structure Row where
  owner : Owner
  geometry : Geometry
  label : Label
  deriving DecidableEq, Repr

def rowRelation (r : Row) : Relation := match r.label with
  | .flow => .flow
  | .terminal input => .terminal input
  | .mapped input output => .mapped
      (if r.geometry.input.base = .zero then none else some input)
      (match r.geometry.output with
       | none => none
       | some p => if p.base = .zero then none else some output)

structure Ref where
  owner : Owner
  geometryId : Nat
  label : Label
  deriving DecidableEq, Repr

structure Catalog where
  geometries : List Geometry
  refs : List Ref
  deriving DecidableEq, Repr

def lookup : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n+1 => lookup xs n

/- Executable reference interner; Kotlin will use exact hash lookup, not this
   linear list. Allocation/access laws below do not claim interner CPU bounds. -/
def intern (g : Geometry) : List Geometry → Nat × List Geometry
  | [] => (0, [g])
  | x :: xs => if x = g then (0, x :: xs)
      else let r := intern g xs; (r.1 + 1, x :: r.2)

theorem intern_finds (g : Geometry) (gs : List Geometry) :
    lookup (intern g gs).2 (intern g gs).1 = some g := by
  induction gs with
  | nil => rfl
  | cons x xs ih =>
    simp only [intern]
    split
    · next h => simp [lookup, h]
    · simp only [lookup]; exact ih

theorem intern_keeps (g : Geometry) (gs : List Geometry) (i : Nat) (old : Geometry)
    (h : lookup gs i = some old) : lookup (intern g gs).2 i = some old := by
  induction gs generalizing i with
  | nil => simp [lookup] at h
  | cons x xs ih =>
    simp only [intern]
    split
    · exact h
    · cases i with
      | zero => exact h
      | succ i => exact ih i (by simpa [lookup] using h)

theorem intern_length (g : Geometry) (gs : List Geometry) :
    (intern g gs).2.length ≤ gs.length + 1 := by
  induction gs with
  | nil => simp [intern]
  | cons x xs ih =>
    simp only [intern]
    split <;> simp_all <;> omega

def compileFrom (gs : List Geometry) : List Row → Catalog
  | [] => ⟨gs, []⟩
  | r :: rs =>
      let found := intern r.geometry gs
      let tail := compileFrom found.2 rs
      ⟨tail.geometries, ⟨r.owner, found.1, r.label⟩ :: tail.refs⟩

def compile (rows : List Row) : Catalog := compileFrom [] rows

theorem compile_geometry_bound (rows : List Row) (gs : List Geometry) :
    (compileFrom gs rows).geometries.length ≤ gs.length + rows.length := by
  induction rows generalizing gs with
  | nil => simp [compileFrom]
  | cons r rs ih =>
    have a := ih (intern r.geometry gs).2
    have b := intern_length r.geometry gs
    simp only [compileFrom, List.length_cons]
    omega

theorem empty_start_geometry_bound (rows : List Row) :
    (compile rows).geometries.length ≤ rows.length := by
  simpa [compile] using compile_geometry_bound rows []

def decodeRef (gs : List Geometry) (r : Ref) : Option Row :=
  (lookup gs r.geometryId).map (fun g => ⟨r.owner, g, r.label⟩)

def decodeRefs (gs : List Geometry) : List Ref → Option (List Row)
  | [] => some []
  | r :: rs => do
      let head ← decodeRef gs r
      let tail ← decodeRefs gs rs
      pure (head :: tail)

def decode (c : Catalog) : Option (List Row) := decodeRefs c.geometries c.refs

theorem compile_keeps_geometry (rows : List Row) (gs : List Geometry) (i : Nat)
    (g : Geometry) (h : lookup gs i = some g) :
    lookup (compileFrom gs rows).geometries i = some g := by
  induction rows generalizing gs with
  | nil => exact h
  | cons r rs ih =>
    exact ih (intern r.geometry gs).2 (intern_keeps r.geometry gs i g h)

theorem compileFrom_decode (rows : List Row) (gs : List Geometry) :
    decode (compileFrom gs rows) = some rows := by
  induction rows generalizing gs with
  | nil => rfl
  | cons r rs ih =>
    simp only [compileFrom, decode, decodeRefs, decodeRef]
    rw [compile_keeps_geometry rs (intern r.geometry gs).2 (intern r.geometry gs).1
      r.geometry (intern_finds r.geometry gs)]
    have htail := ih (intern r.geometry gs).2
    simp only [decode] at htail
    rw [htail]
    rfl

theorem complete_ordered_decode (rows : List Row) : decode (compile rows) = some rows :=
  compileFrom_decode rows []

theorem ref_count_preserved (rows : List Row) (gs : List Geometry) :
    (compileFrom gs rows).refs.length = rows.length := by
  induction rows generalizing gs with
  | nil => rfl
  | cons r rs ih => simpa [compileFrom] using congrArg Nat.succ (ih (intern r.geometry gs).2)

/- Query plans are the old ordered candidate ordinal streams. They can contain
   duplicates, e.g. shared B appears in more than one scoped union. -/
def atRows (rows : List Row) (ids : List Nat) : List Row :=
  ids.filterMap (lookup rows)

def query (rows : List Row) (ids : List Nat) (keep : Row → Bool) : List Row :=
  (atRows rows ids).filter keep

def catalogQuery (c : Catalog) (ids : List Nat) (keep : Row → Bool) : List Row :=
  query ((decode c).getD []) ids keep

theorem all_query_streams_equal (rows : List Row) (ids : List Nat) (keep : Row → Bool) :
    catalogQuery (compile rows) ids keep = query rows ids keep := by
  simp [catalogQuery, complete_ordered_decode]

/- A callback can stop at its first false result. The exact consumed row stream
   and final accumulator, not merely a set, are observations. -/
def visitUntil (step : σ → Row → σ × Bool) : σ → List Row → σ × List Row
  | s, [] => (s, [])
  | s, r :: rs =>
      let next := step s r
      if next.2 then let rest := visitUntil step next.1 rs; (rest.1, r :: rest.2)
      else (next.1, [r])

theorem callback_trace_equal (rows : List Row) (ids : List Nat) (keep : Row → Bool)
    (step : σ → Row → σ × Bool) (start : σ) :
    visitUntil step start (catalogQuery (compile rows) ids keep) =
      visitUntil step start (query rows ids keep) := by
  rw [all_query_streams_equal]

theorem index_plan_equal (rows : List Row) (plan : List Row → List Nat) :
    plan ((decode (compile rows)).getD []) = plan rows := by
  simp [complete_ordered_decode]

structure Query where
  ids : List Nat
  keep : Row → Bool

def oldOracle (rows : List Row) (q : Query) : List Row := query rows q.ids q.keep

def newOracle (c : Catalog) (q : Query) : List Row := catalogQuery c q.ids q.keep

theorem complete_oracle_equal (rows : List Row) :
    newOracle (compile rows) = oldOracle rows := by
  funext q
  exact all_query_streams_equal rows q.ids q.keep

def iterate (oracle : Query → List Row) (ask : σ → Query)
    (step : σ → List Row → σ) : Nat → σ → σ
  | 0, s => s
  | n+1, s => iterate oracle ask step n (step s (oracle (ask s)))

theorem all_composition_prefixes_equal (rows : List Row) (ask : σ → Query)
    (step : σ → List Row → σ) (fuel : Nat) (start : σ) :
    iterate (newOracle (compile rows)) ask step fuel start =
      iterate (oldOracle rows) ask step fuel start := by
  rw [complete_oracle_equal]

theorem estimate_count_equal (rows : List Row) (ids : List Nat) (keep : Row → Bool) :
    (catalogQuery (compile rows) ids keep).length = (query rows ids keep).length := by
  rw [all_query_streams_equal]

theorem existence_equal (rows : List Row) (ids : List Nat) (keep : Row → Bool) :
    (catalogQuery (compile rows) ids keep).isEmpty = (query rows ids keep).isEmpty := by
  rw [all_query_streams_equal]

/- Full static-composition / BFS behavior is a deterministic state transition on
   the ordered oracle result. No new AP algebra or graph search is postulated. -/
def execute (oracle : List Row) (step : σ → Row → σ) (s : σ) : σ := oracle.foldl step s

theorem complete_composition_step_equal (rows : List Row) (ids : List Nat)
    (keep : Row → Bool) (step : σ → Row → σ) (s : σ) :
    execute (catalogQuery (compile rows) ids keep) step s = execute (query rows ids keep) step s := by
  rw [all_query_streams_equal]

def ownerRows (rows : List Row) (owner : Owner) : List Row :=
  rows.filter (fun r => decide (r.owner = owner))

theorem complete_owner_equal (rows : List Row) (owner : Owner) :
    ownerRows ((decode (compile rows)).getD []) owner = ownerRows rows owner := by
  simp [complete_ordered_decode]

/- Normalization is intentionally a supplied executable old adapter, not a new
   rule. Equality holds for every result of that adapter, including first-kept
   normalized duplicate streams, private B and bound-extra insertions. -/
theorem normalized_ingestion_equal (normalize : α → List Row) (raw : α) :
    decode (compile (normalize raw)) = some (normalize raw) := complete_ordered_decode _

theorem added_extras_equal (base extra : List Row) :
    decode (compile (base ++ extra)) = some (base ++ extra) := complete_ordered_decode _

theorem all_geometry_metadata_equal (rows : List Row) :
    ((decode (compile rows)).getD []).map Row.geometry = rows.map Row.geometry := by
  simp [complete_ordered_decode]

theorem derived_relations_equal (rows : List Row) :
    ((decode (compile rows)).getD []).map rowRelation = rows.map rowRelation := by
  simp [complete_ordered_decode]

theorem exact_mark_relations_equal (rows : List Row) :
    ((decode (compile rows)).getD []).map Row.label = rows.map Row.label := by
  simp [complete_ordered_decode]

/- Typed examples expose mistakes which a product-of-marks or ZERO/terminal
   encoding would hide. They use a concrete finite witness. -/
def node (base : Base) (fields : List Nat) (tail : Tail := .star) : Endpoint :=
  ⟨base, fields, tail, []⟩
def own : Owner := ⟨7, [19], 3, -5, -2, .writer⟩
def geo : Geometry := ⟨node (.other 1) [], some (node .static [11,12])⟩
def zeroGeo : Geometry := ⟨node .zero [] .exact, some (node .static [11,12])⟩
def termGeo : Geometry := ⟨node .static [11,12], none⟩
def markedRows : List Row :=
  [⟨own, geo, .mapped 2 5⟩, ⟨own, geo, .mapped 3 6⟩]

theorem no_cartesian_mark_pairs :
    decode (compile markedRows) = some markedRows := by decide

theorem zero_is_not_terminal :
    (Row.mk own zeroGeo (.mapped 0 5)) ≠
      (Row.mk { own with family := .terminal } termGeo (.terminal 5)) := by decide

theorem actual_zero_slot_derived_as_null_relation :
    rowRelation ⟨own, zeroGeo, .mapped 0 5⟩ = .mapped none (some 5) := by decide

theorem actual_zero_slot_is_nonzero_word (radix : Nat) (hr : 1 < radix) :
    pairWord radix (markCode (some 0)) (markCode (some 5)) ≠ 0 := by
  simp only [pairWord, markCode]
  omega

theorem full_context_kept :
    ownerRows [⟨own, geo, .flow⟩] { own with context := [20] } = [] := by decide

theorem producer_exit_kept :
    ownerRows [⟨own, geo, .flow⟩] { own with exit := -5 } = [] := by decide

theorem no_fabricated_mark_pair :
    query markedRows [0,1] (fun r => decide (r.label = .mapped 2 6)) = [] := by decide

def reverseOwner (o : Owner) : Owner := { o with entry := o.exit, exit := o.entry }

theorem producer_ports_reverse_exactly (o : Owner) :
    (reverseOwner o).entry = o.exit ∧ (reverseOwner o).exit = o.entry := by simp [reverseOwner]

theorem reverse_owner_twice (o : Owner) : reverseOwner (reverseOwner o) = o := rfl

theorem empty_entered_boundary_rows : decode (compile []) = some [] := rfl

/- Explicit allocation-unit model. It counts metadata copies, rich-row headers
   and primitive references; it is not a byte-accurate JVM/GC cost model. -/
inductive Read where
  | saveGeometry | savePrimitiveRow | richRow
  deriving DecidableEq, Repr

def eagerBuild (n : Nat) : List Read := List.replicate n .richRow

def packedBuild (g n : Nat) : List Read :=
  List.replicate g .saveGeometry ++ List.replicate n .savePrimitiveRow

def richCount : List Read → Nat
  | [] => 0
  | .richRow :: xs => richCount xs + 1
  | _ :: xs => richCount xs

theorem rich_count_append (xs ys : List Read) : richCount (xs ++ ys) = richCount xs + richCount ys := by
  induction xs with
  | nil => simp only [List.nil_append, richCount, Nat.zero_add]
  | cons x xs ih =>
    cases x <;> simp only [List.cons_append, richCount, ih] <;> omega

theorem eager_materializes_all (n : Nat) : richCount (eagerBuild n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold eagerBuild at *
    rw [List.replicate_succ]
    change richCount (List.replicate n Read.richRow) + 1 = n+1
    rw [ih]

theorem geometry_save_not_rich (n : Nat) : richCount (List.replicate n .saveGeometry) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    exact ih

theorem primitive_save_not_rich (n : Nat) : richCount (List.replicate n .savePrimitiveRow) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    exact ih

theorem packed_materializes_no_rich_rows (g n : Nat) : richCount (packedBuild g n) = 0 := by
  rw [packedBuild, rich_count_append, geometry_save_not_rich, primitive_save_not_rich]

def selectedMaterialization (rows : List Row) (ids : List Nat) (keep : Row → Bool) : List Read :=
  List.replicate (query rows ids keep).length .richRow

theorem lookup_materializes_selected_only (rows : List Row) (ids : List Nat) (keep : Row → Bool) :
    richCount (selectedMaterialization rows ids keep) = (query rows ids keep).length := by
  exact eager_materializes_all _

def eagerVolume (n : Nat) : Nat := 3 * n

def packedVolume (geometryCount rowCount : Nat) : Nat := geometryCount + rowCount

theorem strict_shared_geometry_volume (g n : Nat) (hgn : g ≤ n) (hn : 0 < n) :
    packedVolume g n < eagerVolume n := by
  unfold packedVolume eagerVolume
  omega

theorem one_geometry_many_marks (n : Nat) :
    packedVolume 1 (n+1) = n+2 ∧ eagerVolume (n+1) = 3*n+3 := by
  constructor
  · unfold packedVolume
    omega
  · unfold eagerVolume
    omega

theorem selected_materialization_bound (rows : List Row) (ids : List Nat) (keep : Row → Bool) :
    richCount (selectedMaterialization rows ids keep) ≤ ids.length := by
  rw [lookup_materializes_selected_only]
  exact Nat.le_trans (List.length_filter_le keep (atRows rows ids))
    (List.length_filterMap_le (lookup rows) ids)

def eagerPathVolume (rows pathCost : Nat) : Nat := rows * pathCost + rows

def packedPathVolume (geometries rows pathCost : Nat) : Nat := geometries * pathCost + rows

theorem one_geometry_path_saving (n pathCost : Nat) :
    eagerPathVolume (n+1) pathCost = packedPathVolume 1 (n+1) pathCost + n*pathCost := by
  simp [eagerPathVolume, packedPathVolume, Nat.add_mul]
  omega

theorem one_geometry_path_saving_positive (n pathCost : Nat) (hn : 0 < n) (hp : 0 < pathCost) :
    packedPathVolume 1 (n+1) pathCost < eagerPathVolume (n+1) pathCost := by
  rw [one_geometry_path_saving]
  have h : 0 < n * pathCost := Nat.mul_pos hn hp
  omega

end PackedStaticGuidance
