/-
Source model of embedRawProtection, not a DATA-normalization model.
One invocation fixes owner/full P/base/layer. Coord is an opaque complete
(path,full mark) identity. Header E is an opaque canonical identity, 0=Empty.
Ordered bags model mask union by membership; exact protection allocations are
also counted, so duplicate effective EXACT flags cannot hide behind set union.

DATA is arbitrary ordered input. The native adapter supplies canonical
EXACT-only DATA wrappers. DAG algebra, that wrapper invariant, and refinement
of this deferred-write presentation to the mutable Kotlin loops remain native
adapter obligations; no DATA confluence/idempotence premise is assumed.
-/
import Std

namespace EmbedRawProtectionOrdered

abbrev Coord := Nat
inductive Header where
  | any
  | must (e : Nat)
  | star (e : Nat)
deriving DecidableEq, Repr

def canonicalExact : Header := .must 0

inductive Key where
  | exact (coord : Coord)
  | span (header : Header) (coord : Coord)
deriving DecidableEq, Repr

structure Data where
  header : Header
  exacts : List Coord := []
  spans : List Coord := []
deriving DecidableEq, Repr

structure Source where
  header : Header
  exactFlags : List Coord := []
  spanFlags : List Coord := []
deriving DecidableEq, Repr

structure Row where
  header : Header
  dataExact : List Coord := []
  dataSpan : List Coord := []
  exactFlags : List Coord := []
  spanFlags : List Coord := []
deriving DecidableEq, Repr

def unique [DecidableEq α] : List α → List α
  | [] => []
  | a :: rest => if a ∈ unique rest then unique rest else a :: unique rest

def sourceExact (sources : List Source) : List Coord :=
  sources.flatMap Source.exactFlags

def allExact (sources : List Source) : List Coord := unique (sourceExact sources)

def rowFlags (row : Row) : List Key :=
  row.exactFlags.map Key.exact ++ row.spanFlags.map (Key.span row.header)

def rowPayload (row : Row) : List Key :=
  row.dataExact.map Key.exact ++ row.dataSpan.map (Key.span row.header) ++ rowFlags row

def flags : List Row → List Key
  | [] => []
  | row :: rest => rowFlags row ++ flags rest

def payload : List Row → List Key
  | [] => []
  | row :: rest => rowPayload row ++ payload rest

def countExact (coord : Coord) : List Row → Nat
  | [] => 0
  | row :: rest => row.exactFlags.count coord + countExact coord rest

def fromData (value : Data) : Row :=
  ⟨value.header,value.exacts,value.spans,[],[]⟩

def spanRow (source : Source) : Row :=
  ⟨source.header,[],[],[],source.spanFlags⟩

def exactRow (header : Header) (coord : Coord) : Row :=
  ⟨header,[],[],[coord],[]⟩

/-- Canonical native EXACT-only DATA has the canonical wrapper. A mixed
DATA row keeps its current header. No E operation occurs here. -/
def dataHeader (value : Data) : Header :=
  if value.spans.isEmpty then canonicalExact else value.header

/-- Remove only repeated protected EXACT payload slots, as the Kotlin DATA
loop does. Unprotected duplicates are not removed by this operation. -/
def lowerData (requested seen : List Coord) : List Data → List Data
  | [] => []
  | value :: rest =>
    let kept := value.exacts.filter fun c => !(decide (c ∈ requested ∧ c ∈ seen))
    let next := seen ++ value.exacts.filter (fun c => decide (c ∈ requested))
    let remaining := lowerData requested next rest
    if kept.isEmpty && value.spans.isEmpty then remaining
    else ⟨dataHeader value,kept,value.spans⟩ :: remaining

def spanRows : List Source → List Row
  | [] => []
  | source :: rest =>
    match source.spanFlags with
    | [] => spanRows rest
    | _ :: _ => spanRow source :: spanRows rest

def firstData : List Data → Coord → Option Header
  | [], _ => none
  | value :: rest, coord =>
    if coord ∈ value.exacts then some value.header else firstData rest coord

def firstOriginal (headers : List Header) : List Source → Coord → Option Header
  | [], _ => none
  | source :: rest, coord =>
    if coord ∈ source.exactFlags ∧ source.header ∈ headers then some source.header
    else firstOriginal headers rest coord

def baseRows (data : List Data) (sources : List Source) : List Row :=
  (lowerData (allExact sources) [] data).map fromData ++ spanRows sources

def chooseExact (data : List Data) (sources : List Source) (coord : Coord) : Header :=
  let current := lowerData (allExact sources) [] data
  match firstData current coord with
  | some header => header
  | none =>
    match firstOriginal ((baseRows data sources).map Row.header) sources coord with
    | some header => header
    | none => canonicalExact

/-- Deferred flag writes preserve the first DATA location; original-cohort
choices only target already-existing headers. Only fallback may add a key.
Native exact mask writes happen during the loops; this model records their
coordinate allocation once and coalesces the final writes by header. -/
def rawRows (data : List Data) (sources : List Source) : List Row :=
  baseRows data sources ++
    (allExact sources).map (fun c => exactRow (chooseExact data sources c) c)

def mergeRows (old offered : Row) : Row :=
  ⟨old.header,old.dataExact ++ offered.dataExact,old.dataSpan ++ offered.dataSpan,
    old.exactFlags ++ offered.exactFlags,old.spanFlags ++ offered.spanFlags⟩

def insertRow (offered : Row) : List Row → List Row
  | [] => [offered]
  | old :: rest =>
    if offered.header = old.header then mergeRows old offered :: rest
    else old :: insertRow offered rest

def coalesceAux (current : List Row) : List Row → List Row
  | [] => current
  | row :: rest => coalesceAux (insertRow row current) rest

def coalesce (rows : List Row) : List Row := coalesceAux [] rows
def embed (data : List Data) (sources : List Source) : List Row := coalesce (rawRows data sources)

def inputH (sources : List Source) : List Key :=
  (sourceExact sources).map Key.exact ++ flags (spanRows sources)

def nativeEmbed (data : List Data) (sources : List Source) : List Row :=
  if inputH sources = [] then data.map fromData else embed data sources

def clippedFlags (rows : List Row) : List Key :=
  (flags rows).filter fun key => decide (key ∈ payload rows)

theorem unique_mem (xs : List Coord) (coord : Coord) :
    coord ∈ unique xs ↔ coord ∈ xs := by
  induction xs generalizing coord with
  | nil => simp [unique]
  | cons a rest ih =>
    by_cases ha : a ∈ unique rest
    · rw [unique,if_pos ha]
      constructor
      · intro present
        exact List.mem_cons_of_mem _ ((ih coord).mp present)
      · intro present
        rcases List.mem_cons.mp present with same | later
        · subst coord
          exact ha
        · exact (ih coord).mpr later
    · simpa only [unique,if_neg ha,List.mem_cons] using
        (or_congr (Iff.rfl : coord = a ↔ coord = a) (ih coord))

theorem unique_nodup (xs : List Coord) : (unique xs).Nodup := by
  induction xs with
  | nil => simp [unique]
  | cons a rest ih =>
    by_cases ha : a ∈ unique rest
    · simpa [unique,ha] using ih
    · simpa [unique,ha] using (List.nodup_cons.mpr ⟨ha,ih⟩)

theorem allExact_mem (sources : List Source) (coord : Coord) :
    coord ∈ allExact sources ↔ ∃ source ∈ sources, coord ∈ source.exactFlags := by
  simp [allExact,sourceExact,unique_mem]

theorem effective_EXACT_ignores_wrapper (a b : Header) (coord : Coord) :
    rowFlags (exactRow a coord) = rowFlags (exactRow b coord) := rfl

theorem span_key_retains_header (header : Header) (coord : Coord) :
    Key.span header coord = Key.span header coord := rfl

theorem data_first_match (value : Data) (rest : List Data) (coord : Coord)
    (present : coord ∈ value.exacts) : firstData (value :: rest) coord = some value.header := by
  simp [firstData,present]

theorem data_skip_nonmatch (value : Data) (rest : List Data) (coord : Coord)
    (absent : coord ∉ value.exacts) : firstData (value :: rest) coord = firstData rest coord := by
  simp [firstData,absent]

theorem firstData_has_witness (rows : List Data) (coord : Coord) (header : Header)
    (found : firstData rows coord = some header) :
    ∃ row ∈ rows, row.header = header ∧ coord ∈ row.exacts := by
  induction rows generalizing header with
  | nil => simp [firstData] at found
  | cons row rest ih =>
    by_cases present : coord ∈ row.exacts
    · have eq : row.header = header := by simpa [firstData,present] using found
      exact ⟨row,by simp,eq,present⟩
    · have next : firstData rest coord = some header := by simpa [firstData,present] using found
      obtain ⟨value,member,same,hit⟩ := ih header next
      exact ⟨value,List.mem_cons_of_mem _ member,same,hit⟩

theorem firstOriginal_has_witness (headers : List Header) (sources : List Source)
    (coord : Coord) (header : Header)
    (found : firstOriginal headers sources coord = some header) :
    ∃ source ∈ sources, source.header = header ∧ coord ∈ source.exactFlags ∧ header ∈ headers := by
  induction sources generalizing header with
  | nil => simp [firstOriginal] at found
  | cons source rest ih =>
    by_cases present : coord ∈ source.exactFlags ∧ source.header ∈ headers
    · have same : source.header = header := by simpa [firstOriginal,present] using found
      exact ⟨source,by simp,same,present.1,same ▸ present.2⟩
    · have next : firstOriginal headers rest coord = some header := by
        simpa [firstOriginal,present] using found
      obtain ⟨value,member,same,hit,existing⟩ := ih header next
      exact ⟨value,List.mem_cons_of_mem _ member,same,hit,existing⟩

theorem exact_DATA_priority (data : List Data) (sources : List Source) (coord : Coord) (header : Header)
    (found : firstData (lowerData (allExact sources) [] data) coord = some header) :
    chooseExact data sources coord = header := by simp [chooseExact,found]

theorem exact_existing_original_priority (data : List Data) (sources : List Source)
    (coord : Coord) (header : Header)
    (missing : firstData (lowerData (allExact sources) [] data) coord = none)
    (found : firstOriginal ((baseRows data sources).map Row.header) sources coord = some header) :
    chooseExact data sources coord = header := by simp [chooseExact,missing,found]

theorem exact_fallback_only_after_both_searches (data : List Data) (sources : List Source) (coord : Coord)
    (missing : firstData (lowerData (allExact sources) [] data) coord = none)
    (absent : firstOriginal ((baseRows data sources).map Row.header) sources coord = none) :
    chooseExact data sources coord = canonicalExact := by simp [chooseExact,missing,absent]

theorem flags_append (a b : List Row) : flags (a ++ b) = flags a ++ flags b := by
  induction a with
  | nil => rfl
  | cons row rest ih => simp [flags,ih,List.append_assoc]

theorem data_rows_have_no_flags (data : List Data) : flags (data.map fromData) = [] := by
  induction data with
  | nil => rfl
  | cons value rest ih => simp [flags,fromData,rowFlags,ih]

theorem exactRows_mem (pick : Coord → Header) (coords : List Coord) (coord : Coord) :
    Key.exact coord ∈ flags (coords.map fun c => exactRow (pick c) c) ↔ coord ∈ coords := by
  induction coords with
  | nil => simp [flags]
  | cons c rest ih =>
    change Key.exact coord ∈ rowFlags (exactRow (pick c) c) ++
      flags (rest.map fun c => exactRow (pick c) c) ↔ coord ∈ c :: rest
    rw [List.mem_append,ih]
    simp [exactRow,rowFlags]

theorem exactRows_no_spans (pick : Coord → Header) (coords : List Coord)
    (header : Header) (coord : Coord) :
    Key.span header coord ∉ flags (coords.map fun c => exactRow (pick c) c) := by
  induction coords with
  | nil => simp [flags]
  | cons c rest ih =>
    change Key.span header coord ∉ rowFlags (exactRow (pick c) c) ++
      flags (rest.map fun c => exactRow (pick c) c)
    intro present
    rcases List.mem_append.mp present with here | later
    · simpa [exactRow,rowFlags] using here
    · exact ih later

theorem spanRows_no_exact (sources : List Source) (coord : Coord) :
    Key.exact coord ∉ flags (spanRows sources) := by
  induction sources with
  | nil => simp [spanRows,flags]
  | cons source rest ih =>
    cases hs : source.spanFlags with
    | nil => simp [spanRows,hs,ih]
    | cons c tail => simp [spanRows,hs,flags,spanRow,rowFlags,ih]

theorem spanRows_literal_header (sources : List Source) (header : Header) (coord : Coord) :
    Key.span header coord ∈ flags (spanRows sources) ↔
      ∃ source ∈ sources, source.header = header ∧ coord ∈ source.spanFlags := by
  induction sources with
  | nil => simp [spanRows,flags]
  | cons source rest ih =>
    cases hs : source.spanFlags with
    | nil => simp [spanRows,hs,ih]
    | cons c tail =>
      have expanded : spanRows (source :: rest) = spanRow source :: spanRows rest := by
        simp [spanRows,hs]
      rw [expanded]
      change (Key.span header coord ∈ rowFlags (spanRow source) ++ flags (spanRows rest)) ↔
        ∃ value ∈ source :: rest, value.header = header ∧ coord ∈ value.spanFlags
      constructor
      · intro present
        rcases List.mem_append.mp present with here | later
        · have mapped : Key.span header coord ∈ source.spanFlags.map (Key.span source.header) := by
            simpa only [spanRow,rowFlags,List.map_nil,List.nil_append] using here
          obtain ⟨value,member,same⟩ := List.mem_map.mp mapped
          have equalities : source.header = header ∧ value = coord := by simpa using same
          exact ⟨source,by simp,equalities.1,equalities.2 ▸ member⟩
        · obtain ⟨value,member,same,hit⟩ := ih.mp later
          exact ⟨value,List.mem_cons_of_mem _ member,same,hit⟩
      · rintro ⟨value,member,same,hit⟩
        rcases List.mem_cons.mp member with first | later
        · subst value
          have mapped : Key.span header coord ∈ source.spanFlags.map (Key.span source.header) :=
            List.mem_map.mpr ⟨coord,hit,by rw [same]⟩
          exact List.mem_append_left _ (by
            simpa only [spanRow,rowFlags,List.map_nil,List.nil_append] using mapped)
        · exact List.mem_append_right _ (ih.mpr ⟨value,later,same,hit⟩)

theorem raw_exact_literal_union (data : List Data) (sources : List Source) (coord : Coord) :
    Key.exact coord ∈ flags (rawRows data sources) ↔
      ∃ source ∈ sources, coord ∈ source.exactFlags := by
  simp [rawRows,baseRows,flags_append,data_rows_have_no_flags,spanRows_no_exact,
    exactRows_mem,allExact_mem]

theorem raw_span_literal_union (data : List Data) (sources : List Source)
    (header : Header) (coord : Coord) :
    Key.span header coord ∈ flags (rawRows data sources) ↔
      ∃ source ∈ sources, source.header = header ∧ coord ∈ source.spanFlags := by
  simp [rawRows,baseRows,flags_append,data_rows_have_no_flags,exactRows_no_spans,spanRows_literal_header]

theorem merge_flags_membership (a b : Row) (same : b.header = a.header) (key : Key) :
    key ∈ rowFlags (mergeRows a b) ↔ key ∈ rowFlags a ∨ key ∈ rowFlags b := by
  simp [mergeRows,rowFlags,List.map_append,same,List.mem_append,or_assoc,or_comm,or_left_comm]

theorem insert_flags_membership (offered : Row) (rows : List Row) (key : Key) :
    key ∈ flags (insertRow offered rows) ↔ key ∈ rowFlags offered ∨ key ∈ flags rows := by
  induction rows with
  | nil => simp [insertRow,flags]
  | cons old rest ih =>
    by_cases same : offered.header = old.header
    · simp [insertRow,same,flags,merge_flags_membership _ _ same,
        or_assoc,or_comm,or_left_comm]
    · simp [insertRow,same,flags,ih,or_assoc,or_comm,or_left_comm]

theorem coalesceAux_flags_membership (current rows : List Row) (key : Key) :
    key ∈ flags (coalesceAux current rows) ↔ key ∈ flags current ∨ key ∈ flags rows := by
  induction rows generalizing current with
  | nil => simp [coalesceAux,flags]
  | cons row rest ih =>
    simp [coalesceAux,ih,insert_flags_membership,flags,or_assoc,or_comm,or_left_comm]

theorem coalesce_flags_membership (rows : List Row) (key : Key) :
    key ∈ flags (coalesce rows) ↔ key ∈ flags rows := by
  simp [coalesce,coalesceAux_flags_membership,flags]

theorem H_exact_literal_union (data : List Data) (sources : List Source) (coord : Coord) :
    Key.exact coord ∈ flags (embed data sources) ↔
      ∃ source ∈ sources, coord ∈ source.exactFlags := by
  rw [embed,coalesce_flags_membership,raw_exact_literal_union]

theorem H_span_literal_union (data : List Data) (sources : List Source)
    (header : Header) (coord : Coord) :
    Key.span header coord ∈ flags (embed data sources) ↔
      ∃ source ∈ sources, source.header = header ∧ coord ∈ source.spanFlags := by
  rw [embed,coalesce_flags_membership,raw_span_literal_union]

theorem embed_H_inventory (data : List Data) (sources : List Source) (key : Key) :
    key ∈ flags (embed data sources) ↔ key ∈ inputH sources := by
  cases key with
  | exact coord =>
    simp [H_exact_literal_union,inputH,spanRows_no_exact,sourceExact]
  | span header coord =>
    simp [H_span_literal_union,inputH,spanRows_literal_header]

theorem native_H_inventory (data : List Data) (sources : List Source) (key : Key) :
    key ∈ flags (nativeEmbed data sources) ↔ key ∈ inputH sources := by
  unfold nativeEmbed
  split
  · rename_i absent
    simp [data_rows_have_no_flags,absent]
  · exact embed_H_inventory data sources key

theorem no_H_fast_path_returns_DATA (data : List Data) (sources : List Source)
    (absent : inputH sources = []) : nativeEmbed data sources = data.map fromData := by
  simp [nativeEmbed,absent]

theorem H_exact_no_invention (data : List Data) (sources : List Source) (coord : Coord)
    (absent : ∀ source ∈ sources, coord ∉ source.exactFlags) :
    Key.exact coord ∉ flags (embed data sources) := by
  rw [H_exact_literal_union]
  rintro ⟨source,member,present⟩
  exact absent source member present

theorem H_span_no_invention (data : List Data) (sources : List Source)
    (header : Header) (coord : Coord)
    (absent : ∀ source ∈ sources, source.header = header → coord ∉ source.spanFlags) :
    Key.span header coord ∉ flags (embed data sources) := by
  rw [H_span_literal_union]
  rintro ⟨source,member,same,present⟩
  exact absent source member same present

theorem row_flags_in_payload (row : Row) (key : Key) (present : key ∈ rowFlags row) :
    key ∈ rowPayload row := by simp [rowPayload,present]

theorem flags_in_payload (rows : List Row) (key : Key) (present : key ∈ flags rows) :
    key ∈ payload rows := by
  induction rows generalizing key with
  | nil => simp [flags] at present
  | cons row rest ih =>
    simp only [flags,List.mem_append] at present
    rcases present with here | later
    · exact List.mem_append_left _ (row_flags_in_payload row key here)
    · exact List.mem_append_right _ (ih key later)

theorem payload_before_mask_clipping (rows : List Row) (key : Key) :
    key ∈ clippedFlags rows ↔ key ∈ flags rows := by
  simp only [clippedFlags,List.mem_filter,decide_eq_true_eq]
  constructor
  · exact And.left
  · intro present
    exact ⟨present,flags_in_payload rows key present⟩

theorem countExact_append (coord : Coord) (a b : List Row) :
    countExact coord (a ++ b) = countExact coord a + countExact coord b := by
  induction a with
  | nil => simp [countExact]
  | cons row rest ih => simp [countExact,ih,Nat.add_assoc]

theorem countExact_insert (coord : Coord) (offered : Row) (rows : List Row) :
    countExact coord (insertRow offered rows) = offered.exactFlags.count coord + countExact coord rows := by
  induction rows with
  | nil => simp [insertRow,countExact]
  | cons old rest ih =>
    by_cases same : offered.header = old.header
    · simp [insertRow,same,countExact,mergeRows,List.count_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · simp [insertRow,same,countExact,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem countExact_coalesceAux (coord : Coord) (current rows : List Row) :
    countExact coord (coalesceAux current rows) = countExact coord current + countExact coord rows := by
  induction rows generalizing current with
  | nil => simp [coalesceAux,countExact]
  | cons row rest ih =>
    simp [coalesceAux,ih,countExact_insert,countExact,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem countExact_coalesce (coord : Coord) (rows : List Row) :
    countExact coord (coalesce rows) = countExact coord rows := by
  simp [coalesce,countExact_coalesceAux,countExact]

theorem countExact_data_zero (coord : Coord) (data : List Data) :
    countExact coord (data.map fromData) = 0 := by
  induction data with
  | nil => rfl
  | cons value rest ih => simp [countExact,fromData,ih]

theorem countExact_span_zero (coord : Coord) (sources : List Source) :
    countExact coord (spanRows sources) = 0 := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
    cases hs : source.spanFlags with
    | nil => simp [spanRows,hs,ih]
    | cons c tail => simp [spanRows,hs,countExact,spanRow,ih]

theorem countExact_allocations (coord : Coord) (pick : Coord → Header) (coords : List Coord) :
    countExact coord (coords.map fun c => exactRow (pick c) c) = coords.count coord := by
  induction coords with
  | nil => rfl
  | cons c rest ih =>
    change ([c] : List Coord).count coord +
      countExact coord (rest.map fun c => exactRow (pick c) c) = (c :: rest).count coord
    rw [ih]
    simp [List.count_cons,Nat.add_comm]

theorem exact_flag_allocated_at_most_once (data : List Data) (sources : List Source) (coord : Coord) :
    countExact coord (embed data sources) ≤ 1 := by
  have bound : (allExact sources).count coord ≤ 1 :=
    (List.nodup_iff_count.mp (unique_nodup (sourceExact sources))) coord
  simpa [embed,countExact_coalesce,rawRows,baseRows,countExact_append,
    countExact_data_zero,countExact_span_zero,countExact_allocations] using bound

theorem native_exact_flag_allocated_at_most_once (data : List Data)
    (sources : List Source) (coord : Coord) :
    countExact coord (nativeEmbed data sources) ≤ 1 := by
  unfold nativeEmbed
  split
  · simp [countExact_data_zero]
  · exact exact_flag_allocated_at_most_once data sources coord

def hF : Header := .star 1
def hG : Header := .must 2
def sampleData : List Data := [⟨hF,[7],[40]⟩,⟨hG,[7,8],[41]⟩]
def sampleSources : List Source :=
  [⟨hG,[7,8,9],[41]⟩,⟨hF,[9],[40]⟩,⟨.any,[10],[]⟩]

theorem witness_first_DATA_exact : chooseExact sampleData sampleSources 7 = hF := by decide
theorem witness_second_DATA_exact : chooseExact sampleData sampleSources 8 = hG := by decide
theorem witness_existing_original_exact : chooseExact sampleData sampleSources 9 = hG := by decide
theorem witness_exact_only_fallback : chooseExact sampleData sampleSources 10 = canonicalExact := by decide
theorem witness_repeated_DATA_exact_removed :
    lowerData (allExact sampleSources) [] sampleData = [⟨hF,[7],[40]⟩,⟨hG,[8],[41]⟩] := by decide
theorem witness_span_header_not_rewritten :
    Key.span hG 41 ∈ flags (embed sampleData sampleSources) ∧
    Key.span canonicalExact 41 ∉ flags (embed sampleData sampleSources) := by decide

def check : Bool :=
  decide (chooseExact sampleData sampleSources 7 = hF) &&
  decide (chooseExact sampleData sampleSources 8 = hG) &&
  decide (chooseExact sampleData sampleSources 9 = hG) &&
  decide (chooseExact sampleData sampleSources 10 = canonicalExact) &&
  decide (countExact 7 (embed sampleData sampleSources) = 1) &&
  decide (countExact 9 (embed sampleData sampleSources) = 1)

theorem executable_ordered_embedding_witness : check = true := by decide
#eval "ORDERED_EMBED=" ++ toString check

#print axioms unique_mem
#print axioms unique_nodup
#print axioms allExact_mem
#print axioms effective_EXACT_ignores_wrapper
#print axioms span_key_retains_header
#print axioms data_first_match
#print axioms data_skip_nonmatch
#print axioms firstData_has_witness
#print axioms firstOriginal_has_witness
#print axioms exact_DATA_priority
#print axioms exact_existing_original_priority
#print axioms exact_fallback_only_after_both_searches
#print axioms flags_append
#print axioms data_rows_have_no_flags
#print axioms exactRows_mem
#print axioms exactRows_no_spans
#print axioms spanRows_no_exact
#print axioms spanRows_literal_header
#print axioms raw_exact_literal_union
#print axioms raw_span_literal_union
#print axioms merge_flags_membership
#print axioms insert_flags_membership
#print axioms coalesceAux_flags_membership
#print axioms coalesce_flags_membership
#print axioms H_exact_literal_union
#print axioms H_span_literal_union
#print axioms embed_H_inventory
#print axioms native_H_inventory
#print axioms no_H_fast_path_returns_DATA
#print axioms H_exact_no_invention
#print axioms H_span_no_invention
#print axioms row_flags_in_payload
#print axioms flags_in_payload
#print axioms payload_before_mask_clipping
#print axioms countExact_append
#print axioms countExact_insert
#print axioms countExact_coalesceAux
#print axioms countExact_coalesce
#print axioms countExact_data_zero
#print axioms countExact_span_zero
#print axioms countExact_allocations
#print axioms exact_flag_allocated_at_most_once
#print axioms native_exact_flag_allocated_at_most_once
#print axioms witness_first_DATA_exact
#print axioms witness_second_DATA_exact
#print axioms witness_existing_original_exact
#print axioms witness_exact_only_fallback
#print axioms witness_repeated_DATA_exact_removed
#print axioms witness_span_header_not_rewritten
#print axioms executable_ordered_embedding_witness

end EmbedRawProtectionOrdered
