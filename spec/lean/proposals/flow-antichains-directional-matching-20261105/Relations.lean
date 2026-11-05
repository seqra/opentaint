import Std

/-!
Concrete pure NORMAL STAR/FLOW suffix relations. The interface and full mark
are opaque values, preserved exactly. This proves paired relation inclusion,
not a native AP/observer/driver deletion theorem.
-/
namespace FlowAntichains.Relations
set_option autoImplicit false

structure Row (Field : Type) where
  interface : Nat
  inputBase : Nat
  outputBase : Nat
  inputPrefix : List Field
  outputPrefix : List Field
  deriving DecidableEq

structure Pair (Field : Type) where
  interface : Nat
  inputBase : Nat
  outputBase : Nat
  mark : Nat
  inputPath : List Field
  outputPath : List Field

variable {Field : Type}

def produce (row : Row Field) (mark : Nat) (suffix : List Field) : Pair Field :=
  ⟨row.interface, row.inputBase, row.outputBase, mark,
    row.inputPrefix ++ suffix, row.outputPrefix ++ suffix⟩

def denotes (row : Row Field) (pair : Pair Field) : Prop :=
  ∃ suffix, produce row pair.mark suffix = pair

def specialize (row : Row Field) (residual : List Field) : Row Field :=
  { row with inputPrefix := row.inputPrefix ++ residual,
             outputPrefix := row.outputPrefix ++ residual }

/-- Explicit executable witness: use the same residual on both endpoints. -/
def coveringSuffix (residual suffix : List Field) : List Field := residual ++ suffix

theorem produced_specialization (row : Row Field) (residual suffix : List Field) (mark : Nat) :
    produce (specialize row residual) mark suffix =
      produce row mark (coveringSuffix residual suffix) := by
  simp [produce, specialize, coveringSuffix, List.append_assoc]

theorem specialization_subrelation (row : Row Field) (residual : List Field) (pair : Pair Field)
    (member : denotes (specialize row residual) pair) : denotes row pair := by
  obtain ⟨suffix, same⟩ := member
  exact ⟨coveringSuffix residual suffix, (produced_specialization row residual suffix pair.mark).symm.trans same⟩

theorem union_specialization_is_short (row : Row Field) (residual : List Field) (pair : Pair Field) :
    (denotes row pair ∨ denotes (specialize row residual) pair) ↔ denotes row pair := by
  constructor
  · intro member
    rcases member with short | long
    · exact short
    · exact specialization_subrelation row residual pair long
  · exact Or.inl

theorem every_specialization_is_covered (row : Row Field) (residuals : List (List Field))
    (pair : Pair Field) (member : ∃ residual ∈ residuals, denotes (specialize row residual) pair) :
    denotes row pair := by
  obtain ⟨residual, _, long⟩ := member
  exact specialization_subrelation row residual pair long

theorem empty_specialization (row : Row Field) : specialize row [] = row := by
  cases row
  simp [specialize]

theorem specialize_twice (row : Row Field) (left right : List Field) :
    specialize (specialize row left) right = specialize row (left ++ right) := by
  simp [specialize, List.append_assoc]

def reverseGeometry (row : Row Field) : Row Field :=
  { row with inputBase := row.outputBase, outputBase := row.inputBase,
             inputPrefix := row.outputPrefix, outputPrefix := row.inputPrefix }

theorem reverse_geometry_specializes (row : Row Field) (residual : List Field) :
    reverseGeometry (specialize row residual) = specialize (reverseGeometry row) residual := rfl

theorem reverse_specialization_subrelation (row : Row Field) (residual : List Field)
    (pair : Pair Field) (member : denotes (reverseGeometry (specialize row residual)) pair) :
    denotes (reverseGeometry row) pair := by
  exact specialization_subrelation (reverseGeometry row) residual pair member

def counted (weight : Field → Nat) : List Field → Nat
  | [] => 0
  | head :: tail => weight head + counted weight tail

theorem counted_append (weight : Field → Nat) (left right : List Field) :
    counted weight (left ++ right) = counted weight left + counted weight right := by
  induction left with
  | nil => simp [counted]
  | cons head tail ih => simp [counted, ih, Nat.add_assoc]

def grows (weight : Field → Nat) (row : Row Field) : Prop :=
  counted weight row.inputPrefix < counted weight row.outputPrefix

theorem specialization_growth_iff (weight : Field → Nat) (row : Row Field) (residual : List Field) :
    grows weight (specialize row residual) ↔ grows weight row := by
  simp only [grows, specialize, counted_append]
  exact Nat.add_lt_add_iff_right

theorem reverse_specialization_growth_iff (weight : Field → Nat) (row : Row Field)
    (residual : List Field) :
    grows weight (reverseGeometry (specialize row residual)) ↔ grows weight (reverseGeometry row) := by
  exact specialization_growth_iff weight (reverseGeometry row) residual

def strip [DecidableEq Field] : List Field → List Field → Option (List Field)
  | [], path => some path
  | _ :: _, [] => none
  | head :: requested, first :: path => if head = first then strip requested path else none

def applyExact [DecidableEq Field] (row : Row Field) (path : List Field) : Option (List Field) :=
  (strip row.inputPrefix path).map (fun suffix => row.outputPrefix ++ suffix)

theorem strip_append [DecidableEq Field] (requested suffix : List Field) :
    strip requested (requested ++ suffix) = some suffix := by
  induction requested with
  | nil => rfl
  | cons head tail ih => simp [strip, ih]

theorem exact_descendant_applications_equal [DecidableEq Field] (row : Row Field)
    (residual suffix : List Field) :
    applyExact (specialize row residual) ((row.inputPrefix ++ residual) ++ suffix) =
      applyExact row ((row.inputPrefix ++ residual) ++ suffix) := by
  change (strip (row.inputPrefix ++ residual) ((row.inputPrefix ++ residual) ++ suffix)).map
      (fun rest => (row.outputPrefix ++ residual) ++ rest) =
    (strip row.inputPrefix ((row.inputPrefix ++ residual) ++ suffix)).map
      (fun rest => row.outputPrefix ++ rest)
  rw [strip_append, List.append_assoc, strip_append]
  simp [List.append_assoc]

theorem exact_descendant_result [DecidableEq Field] (row : Row Field)
    (residual suffix : List Field) :
    applyExact (specialize row residual) ((row.inputPrefix ++ residual) ++ suffix) =
      some ((row.outputPrefix ++ residual) ++ suffix) := by
  change (strip (row.inputPrefix ++ residual) ((row.inputPrefix ++ residual) ++ suffix)).map
      (fun rest => (row.outputPrefix ++ residual) ++ rest) =
    some ((row.outputPrefix ++ residual) ++ suffix)
  rw [strip_append]
  rfl

def identityRow : Row Nat := ⟨7, 1, 2, [], []⟩
def wrongResidualRow : Row Nat := ⟨7, 1, 2, [10], []⟩

theorem aligned_example :
    applyExact (specialize identityRow [10]) [10, 20] = some [10, 20] ∧
    applyExact identityRow [10, 20] = some [10, 20] := by decide

theorem unaligned_example_changes_result :
    applyExact wrongResidualRow [10, 20] = some [20] ∧
    applyExact identityRow [10, 20] = some [10, 20] := by decide

theorem pair_metadata_preserved (row : Row Field) (residual suffix : List Field) (mark : Nat) :
    (produce (specialize row residual) mark suffix).interface = row.interface ∧
    (produce (specialize row residual) mark suffix).inputBase = row.inputBase ∧
    (produce (specialize row residual) mark suffix).outputBase = row.outputBase ∧
    (produce (specialize row residual) mark suffix).mark = mark := ⟨rfl, rfl, rfl, rfl⟩

/-- Relational cover never creates a shorter row: the left row must already exist. -/
def Covers (short long : Row Field) : Prop := ∃ residual, specialize short residual = long

theorem covers_refl (row : Row Field) : Covers row row := ⟨[], empty_specialization row⟩

theorem covers_trans (first middle last : Row Field)
    (left : Covers first middle) (right : Covers middle last) : Covers first last := by
  obtain ⟨a, rfl⟩ := left
  obtain ⟨b, same⟩ := right
  exact ⟨a ++ b, (specialize_twice first a b).symm.trans same⟩

theorem cover_denotation (short long : Row Field) (cover : Covers short long)
    (pair : Pair Field) (member : denotes long pair) : denotes short pair := by
  obtain ⟨residual, rfl⟩ := cover
  exact specialization_subrelation short residual pair member

theorem strip_sound [DecidableEq Field] (requested path rest : List Field)
    (found : strip requested path = some rest) : path = requested ++ rest := by
  induction requested generalizing path with
  | nil => simpa [strip] using found
  | cons head tail ih =>
    cases path with
    | nil => simp [strip] at found
    | cons first path =>
      by_cases same : head = first
      · subst first
        have below : strip tail path = some rest := by simpa [strip] using found
        exact congrArg (List.cons head) (ih path below)
      · simp [strip, same] at found

def coverWitness [DecidableEq Field] (short long : Row Field) : Option (List Field) :=
  match strip short.inputPrefix long.inputPrefix with
  | none => none
  | some residual => if specialize short residual = long then some residual else none

theorem coverWitness_sound [DecidableEq Field] (short long : Row Field) (residual : List Field)
    (found : coverWitness short long = some residual) : specialize short residual = long := by
  unfold coverWitness at found
  cases located : strip short.inputPrefix long.inputPrefix with
  | none => simp [located] at found
  | some candidate =>
    by_cases same : specialize short candidate = long
    · simp only [located, if_pos same, Option.some.injEq] at found
      subst candidate
      exact same
    · simp [located, same] at found

theorem coverWitness_complete [DecidableEq Field] (short : Row Field) (residual : List Field) :
    coverWitness short (specialize short residual) = some residual := by
  simp [coverWitness, specialize, strip_append]

def coversB [DecidableEq Field] (short long : Row Field) : Bool :=
  (coverWitness short long).isSome

theorem coversB_iff [DecidableEq Field] (short long : Row Field) :
    coversB short long = true ↔ Covers short long := by
  constructor
  · intro present
    unfold coversB at present
    cases found : coverWitness short long with
    | none => simp [found] at present
    | some residual => exact ⟨residual, coverWitness_sound short long residual found⟩
  · rintro ⟨residual, rfl⟩
    simp [coversB, coverWitness_complete]

/-- Head cancellation on reversed paths computes a common suffix in linear depth. -/
structure Factors (Field : Type) where
  inputCore : List Field
  outputCore : List Field
  residual : List Field
  deriving DecidableEq

def cancelHeads [DecidableEq Field] : List Field → List Field → Factors Field
  | head :: left, first :: right =>
      if head = first then
        let rest := cancelHeads left right
        { rest with residual := head :: rest.residual }
      else ⟨head :: left, first :: right, []⟩
  | left, right => ⟨left, right, []⟩

theorem cancelHeads_reconstruct [DecidableEq Field] (left right : List Field) :
    left = (cancelHeads left right).residual ++ (cancelHeads left right).inputCore ∧
    right = (cancelHeads left right).residual ++ (cancelHeads left right).outputCore := by
  induction left generalizing right with
  | nil => simp [cancelHeads]
  | cons head tail ih =>
    cases right with
    | nil => simp [cancelHeads]
    | cons first right =>
      by_cases same : head = first
      · subst first
        have below := ih right
        simpa [cancelHeads] using And.intro (congrArg (List.cons head) below.1)
          (congrArg (List.cons head) below.2)
      · simp [cancelHeads, same]

theorem cancelHeads_common [DecidableEq Field] (common left right : List Field) :
    cancelHeads (common ++ left) (common ++ right) =
      { cancelHeads left right with residual := common ++ (cancelHeads left right).residual } := by
  induction common with
  | nil => rfl
  | cons head tail ih => simp [cancelHeads, ih]

def factorPaths [DecidableEq Field] (left right : List Field) : Factors Field :=
  let reversed := cancelHeads left.reverse right.reverse
  ⟨reversed.inputCore.reverse, reversed.outputCore.reverse, reversed.residual.reverse⟩

theorem factorPaths_reconstruct [DecidableEq Field] (left right : List Field) :
    left = (factorPaths left right).inputCore ++ (factorPaths left right).residual ∧
    right = (factorPaths left right).outputCore ++ (factorPaths left right).residual := by
  have reversed := cancelHeads_reconstruct left.reverse right.reverse
  exact ⟨by simpa [factorPaths, List.reverse_append] using congrArg List.reverse reversed.1,
         by simpa [factorPaths, List.reverse_append] using congrArg List.reverse reversed.2⟩

theorem factorPaths_append [DecidableEq Field] (left right residual : List Field) :
    factorPaths (left ++ residual) (right ++ residual) =
      { factorPaths left right with residual := (factorPaths left right).residual ++ residual } := by
  simp [factorPaths, List.reverse_append, cancelHeads_common]

def factors [DecidableEq Field] (row : Row Field) : Factors Field :=
  factorPaths row.inputPrefix row.outputPrefix

/-- The owner includes exact mode, marks/mx, ports and empty-E eligibility in this key. -/
def family [DecidableEq Field] (row : Row Field) : Nat × Nat × Nat × List Field × List Field :=
  (row.interface, row.inputBase, row.outputBase, (factors row).inputCore, (factors row).outputCore)

theorem family_specialize [DecidableEq Field] (row : Row Field) (residual : List Field) :
    family (specialize row residual) = family row := by
  simp [family, factors, specialize, factorPaths_append]

theorem residual_specialize [DecidableEq Field] (row : Row Field) (residual : List Field) :
    (factors (specialize row residual)).residual = (factors row).residual ++ residual := by
  simp [factors, specialize, factorPaths_append]

def IndexCovers [DecidableEq Field] (short long : Row Field) : Prop :=
  family short = family long ∧ (factors short).residual.IsPrefix (factors long).residual

theorem cover_has_index_witness [DecidableEq Field] (short long : Row Field)
    (cover : Covers short long) : IndexCovers short long := by
  obtain ⟨residual, rfl⟩ := cover
  exact ⟨(family_specialize short residual).symm, ⟨residual, (residual_specialize short residual).symm⟩⟩

theorem index_witness_is_cover [DecidableEq Field] (short long : Row Field)
    (indexed : IndexCovers short long) : Covers short long := by
  obtain ⟨key, residual, sameResidual⟩ := indexed
  have sameInterface : short.interface = long.interface := congrArg Prod.fst key
  have sameInput : short.inputBase = long.inputBase := congrArg (fun k => k.2.1) key
  have sameOutput : short.outputBase = long.outputBase := congrArg (fun k => k.2.2.1) key
  have inputCore : (factors short).inputCore = (factors long).inputCore := congrArg (fun k => k.2.2.2.1) key
  have outputCore : (factors short).outputCore = (factors long).outputCore := congrArg (fun k => k.2.2.2.2) key
  have s := factorPaths_reconstruct short.inputPrefix short.outputPrefix
  have l := factorPaths_reconstruct long.inputPrefix long.outputPrefix
  have inputPath : short.inputPrefix ++ residual = long.inputPrefix := by
    calc
      short.inputPrefix ++ residual =
          ((factors short).inputCore ++ (factors short).residual) ++ residual :=
            congrArg (fun path => path ++ residual) s.1
      _ = (factors long).inputCore ++ (factors long).residual := by
          rw [inputCore, List.append_assoc, sameResidual]
      _ = long.inputPrefix := l.1.symm
  have outputPath : short.outputPrefix ++ residual = long.outputPrefix := by
    calc
      short.outputPrefix ++ residual =
          ((factors short).outputCore ++ (factors short).residual) ++ residual :=
            congrArg (fun path => path ++ residual) s.2
      _ = (factors long).outputCore ++ (factors long).residual := by
          rw [outputCore, List.append_assoc, sameResidual]
      _ = long.outputPrefix := l.2.symm
  refine ⟨residual, ?_⟩
  cases short with
  | mk owner ib ob ip op =>
    cases long with
    | mk owner' ib' ob' ip' op' =>
      simp only [specialize, Row.mk.injEq]
      exact ⟨sameInterface, sameInput, sameOutput, inputPath, outputPath⟩

theorem index_cover_iff [DecidableEq Field] (short long : Row Field) :
    IndexCovers short long ↔ Covers short long :=
  ⟨index_witness_is_cover short long, cover_has_index_witness short long⟩

/-- Prefix-list executable index reference. A child-map trie must implement this predicate. -/
def prefixCandidates [DecidableEq Field] (rows : List (Row Field)) (query : Row Field) : List (Row Field) :=
  rows.filter (fun row => decide (family row = family query) &&
    ((factors row).residual.isPrefixOf (factors query).residual))

theorem prefixCandidates_complete_and_sound [DecidableEq Field] (rows : List (Row Field))
    (query row : Row Field) : row ∈ prefixCandidates rows query ↔ row ∈ rows ∧ Covers row query := by
  simp only [prefixCandidates, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
    List.isPrefixOf_iff_prefix]
  exact and_congr_right (fun _ => index_cover_iff row query)

/-- Below-prefix AP payload handling is shared. Native correspondence is a separate obligation. -/
def applyPayload [DecidableEq Field] {Payload Result : Type} (transform : Payload → Result)
    (row : Row Field) (path : List Field) (payload : Payload) : Option (List Field × Result) :=
  (applyExact row path).map (fun output => (output, transform payload))

theorem below_payload_applications_equal [DecidableEq Field] {Payload Result : Type}
    (transform : Payload → Result) (row : Row Field) (residual suffix : List Field) (payload : Payload) :
    applyPayload transform (specialize row residual) ((row.inputPrefix ++ residual) ++ suffix) payload =
      applyPayload transform row ((row.inputPrefix ++ residual) ++ suffix) payload := by
  unfold applyPayload
  rw [exact_descendant_applications_equal]

theorem below_ordered_packet_applications_equal [DecidableEq Field] {Payload Result : Type}
    (transform : Payload → Result) (row : Row Field) (residual : List Field)
    (leaves : List (List Field × Payload)) :
    leaves.map (fun leaf => applyPayload transform (specialize row residual)
      ((row.inputPrefix ++ residual) ++ leaf.1) leaf.2) =
    leaves.map (fun leaf => applyPayload transform row
      ((row.inputPrefix ++ residual) ++ leaf.1) leaf.2) := by
  apply List.map_congr_left
  intro leaf _
  exact below_payload_applications_equal transform row residual leaf.1 leaf.2

def listDenotes (rows : List (Row Field)) (pair : Pair Field) : Prop :=
  ∃ row ∈ rows, denotes row pair

def Antichain (rows : List (Row Field)) : Prop :=
  ∀ short ∈ rows, ∀ long ∈ rows, Covers short long → short = long

def insert [DecidableEq Field] (rows : List (Row Field)) (offered : Row Field) : List (Row Field) :=
  if rows.any (fun row => coversB row offered) then rows
  else rows.filter (fun row => !coversB offered row) ++ [offered]

theorem insert_never_invents [DecidableEq Field] (rows : List (Row Field)) (offered row : Row Field)
    (member : row ∈ insert rows offered) : row ∈ rows ∨ row = offered := by
  unfold insert at member
  split at member
  · exact Or.inl member
  · rcases List.mem_append.mp member with kept | fresh
    · exact Or.inl (List.mem_filter.mp kept).1
    · exact Or.inr (List.mem_singleton.mp fresh)

theorem insert_covers_every_input [DecidableEq Field] (rows : List (Row Field)) (offered row : Row Field)
    (member : row ∈ rows ∨ row = offered) :
    ∃ representative ∈ insert rows offered, Covers representative row := by
  unfold insert
  split
  next present =>
    rcases member with old | fresh
    · exact ⟨row, old, covers_refl row⟩
    · subst row
      obtain ⟨short, old, covered⟩ := List.any_eq_true.mp present
      exact ⟨short, old, (coversB_iff short offered).mp covered⟩
  next absent =>
    rcases member with old | fresh
    · by_cases covered : coversB offered row = true
      · exact ⟨offered, List.mem_append.mpr (Or.inr (List.mem_singleton_self _)),
          (coversB_iff offered row).mp covered⟩
      · exact ⟨row, List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨old, by simpa using covered⟩)), covers_refl row⟩
    · subst row
      exact ⟨offered, List.mem_append.mpr (Or.inr (List.mem_singleton_self _)), covers_refl offered⟩

theorem insert_preserves_relation [DecidableEq Field] (rows : List (Row Field))
    (offered : Row Field) (pair : Pair Field) :
    listDenotes (insert rows offered) pair ↔ listDenotes rows pair ∨ denotes offered pair := by
  constructor
  · rintro ⟨row, member, fact⟩
    rcases insert_never_invents rows offered row member with old | rfl
    · exact Or.inl ⟨row, old, fact⟩
    · exact Or.inr fact
  · intro fact
    have original : ∃ row, (row ∈ rows ∨ row = offered) ∧ denotes row pair := by
      rcases fact with ⟨row, member, output⟩ | output
      · exact ⟨row, Or.inl member, output⟩
      · exact ⟨offered, Or.inr rfl, output⟩
    obtain ⟨row, member, output⟩ := original
    obtain ⟨representative, kept, cover⟩ := insert_covers_every_input rows offered row member
    exact ⟨representative, kept, cover_denotation representative row cover pair output⟩

theorem insert_antichain [DecidableEq Field] (rows : List (Row Field)) (offered : Row Field)
    (valid : Antichain rows) : Antichain (insert rows offered) := by
  unfold insert
  split
  · exact valid
  next absent =>
    intro short shortMember long longMember cover
    rcases List.mem_append.mp shortMember with shortOld | shortNew
    · have shortFiltered := List.mem_filter.mp shortOld
      rcases List.mem_append.mp longMember with longOld | longNew
      · exact valid short shortFiltered.1 long (List.mem_filter.mp longOld).1 cover
      · have equal := List.mem_singleton.mp longNew
        subst long
        have existsCover : rows.any (fun row => coversB row offered) = true :=
          List.any_eq_true.mpr ⟨short, shortFiltered.1, (coversB_iff short offered).mpr cover⟩
        exact False.elim (absent existsCover)
    · have equal := List.mem_singleton.mp shortNew
      subst short
      rcases List.mem_append.mp longMember with longOld | longNew
      · have filtered := (List.mem_filter.mp longOld).2
        have covered := (coversB_iff offered long).mpr cover
        simp [covered] at filtered
      · exact (List.mem_singleton.mp longNew).symm

def build [DecidableEq Field] : List (Row Field) → List (Row Field) → List (Row Field)
  | current, [] => current
  | current, offered :: rest => build (insert current offered) rest

theorem build_antichain [DecidableEq Field] (input current : List (Row Field))
    (valid : Antichain current) : Antichain (build current input) := by
  induction input generalizing current with
  | nil => exact valid
  | cons offered rest ih => exact ih (insert current offered) (insert_antichain current offered valid)

theorem build_never_invents [DecidableEq Field] (input current : List (Row Field)) (row : Row Field)
    (member : row ∈ build current input) : row ∈ current ∨ row ∈ input := by
  induction input generalizing current with
  | nil => exact Or.inl member
  | cons offered rest ih =>
    rcases ih (insert current offered) member with before | later
    · rcases insert_never_invents current offered row before with old | rfl
      · exact Or.inl old
      · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ later)

theorem build_preserves_relation [DecidableEq Field] (input current : List (Row Field)) (pair : Pair Field) :
    listDenotes (build current input) pair ↔ listDenotes current pair ∨ listDenotes input pair := by
  induction input generalizing current with
  | nil => simp [build, listDenotes]
  | cons offered rest ih =>
    rw [build, ih, insert_preserves_relation]
    simp only [listDenotes, List.mem_cons]
    constructor
    · intro fact
      rcases fact with (old | fresh) | ⟨row, later, output⟩
      · exact Or.inl old
      · exact Or.inr ⟨offered, Or.inl rfl, fresh⟩
      · exact Or.inr ⟨row, Or.inr later, output⟩
    · intro fact
      rcases fact with old | ⟨row, member, output⟩
      · exact Or.inl (Or.inl old)
      · rcases member with rfl | later
        · exact Or.inl (Or.inr output)
        · exact Or.inr ⟨row, later, output⟩

def canonical [DecidableEq Field] (input : List (Row Field)) : List (Row Field) := build [] input

theorem canonical_is_antichain [DecidableEq Field] (input : List (Row Field)) : Antichain (canonical input) :=
  build_antichain input [] (by intro row member; cases member)

theorem canonical_relation [DecidableEq Field] (input : List (Row Field)) (pair : Pair Field) :
    listDenotes (canonical input) pair ↔ listDenotes input pair := by
  simpa [canonical, listDenotes] using build_preserves_relation input [] pair

theorem canonical_has_input_witness [DecidableEq Field] (input : List (Row Field)) (row : Row Field)
    (member : row ∈ canonical input) : row ∈ input := by
  rcases build_never_invents input [] row member with empty | original
  · cases empty
  · exact original

theorem late_short_row_replaces_long_without_inventing_base :
    canonical [specialize identityRow [10], identityRow] = [identityRow] := by decide

theorem long_rows_do_not_invent_missing_base :
    canonical [specialize identityRow [10], specialize identityRow [20]] =
      [specialize identityRow [10], specialize identityRow [20]] := by decide

theorem distinct_interfaces_do_not_merge :
    canonical [identityRow, { identityRow with interface := 8 }] =
      [identityRow, { identityRow with interface := 8 }] := by decide

end FlowAntichains.Relations
