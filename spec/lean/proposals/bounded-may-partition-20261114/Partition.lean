import Policy

/- Investigation model. A finite NORMAL guard partitions a coarse FLOW
   query. These are conditional AP queries, not propagated path evidence.
   STAR regions below describe suffix geometry, not uniform taint. -/
namespace BoundedMayPartition
open NonEmptyPolicy

structure Region where
  path : Path
  tail : Tail
  excluded : List Nat := []
  deriving DecidableEq, Repr

def accepts (q : Region) (point : Path) : Bool :=
  match dropHead q.path point with
  | none => false
  | some suffix => admits q.tail q.excluded suffix

def below (field : Nat) (q : Region) : Region :=
  {q with path := field :: q.path}

/-- The empty point, a residual cone, and the selected child cone. The
    child includes its empty point; this is not the old child-NE ban. -/
def partition : Path → List Region
  | [] => [⟨[], .star, []⟩]
  | field :: rest =>
    [⟨[], .exact, []⟩, ⟨[], .star, [field]⟩] ++
      (partition rest).map (below field)

theorem accepts_below (field : Nat) (q : Region) (point : Path) :
    accepts (below field q) (field :: point) = accepts q point := by
  simp [accepts, below, dropHead]

theorem partition_covers_every_point (guard point : Path) :
    ∃ q ∈ partition guard, accepts q point = true := by
  induction guard generalizing point with
  | nil =>
    refine ⟨⟨[], .star, []⟩, by simp [partition], ?_⟩
    cases point <;> simp [accepts, dropHead, admits] <;> rfl
  | cons field rest ih =>
    cases point with
    | nil =>
      refine ⟨⟨[], .exact, []⟩, by simp [partition], ?_⟩
      rfl
    | cons next suffix =>
      by_cases same : next = field
      · subst next
        rcases ih suffix with ⟨q, member, yes⟩
        refine ⟨below field q, ?_, ?_⟩
        · simp only [partition, List.mem_append, List.mem_map]
          exact Or.inr ⟨q, member, rfl⟩
        · exact (accepts_below field q suffix).trans yes
      · refine ⟨⟨[], .star, [field]⟩, by simp [partition], ?_⟩
        simp [accepts, dropHead, admits, same]
        rfl

theorem partition_query_count (guard : Path) :
    (partition guard).length = 2 * guard.length + 1 := by
  induction guard with
  | nil => rfl
  | cons field rest ih => simp [partition, ih]; omega

theorem partition_path_bound (guard : Path) (q : Region)
    (member : q ∈ partition guard) : q.path.length ≤ guard.length := by
  induction guard generalizing q with
  | nil => simp [partition] at member; subst q; simp
  | cons field rest ih =>
    simp only [partition, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map] at member
    rcases member with (same | same) | ⟨child, inside, same⟩
    · subst q; simp
    · subst q; simp
    · subst q
      simpa [below] using Nat.succ_le_succ (ih child inside)

theorem partition_has_only_exact_or_star (guard : Path) (q : Region)
    (member : q ∈ partition guard) : q.tail = .exact ∨ q.tail = .star := by
  induction guard generalizing q with
  | nil => simp [partition] at member; subst q; exact Or.inr rfl
  | cons field rest ih =>
    simp only [partition, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map] at member
    rcases member with (same | same) | ⟨child, inside, same⟩
    · subst q; exact Or.inl rfl
    · subst q; exact Or.inr rfl
    · subst q; exact ih child inside

/-- Any point-wise transfer/observation can still use its original input.
    This is input coverage, not an assumed native C2/C5 equivalence. -/
theorem partition_preserves_every_point_witness (guard input output : Path)
    (transfer : Path → Path → Prop) (hit : transfer input output) :
    ∃ q ∈ partition guard, accepts q input = true ∧ transfer input output := by
  rcases partition_covers_every_point guard input with ⟨q, inside, yes⟩
  exact ⟨q, inside, yes, hit⟩

theorem partition_preserves_and_reflects_transfer (guard input output : Path)
    (transfer : Path → Path → Prop) :
    transfer input output ↔
      ∃ q ∈ partition guard, accepts q input = true ∧ transfer input output := by
  constructor
  · exact partition_preserves_every_point_witness guard input output transfer
  · rintro ⟨_, _, _, hit⟩; exact hit

theorem split_includes_the_child_root (field : Nat) (rest : Path) :
    ∃ q ∈ partition (field :: rest), accepts q [field] = true :=
  partition_covers_every_point _ _

theorem a_guard_does_not_ban_an_unmentioned_field (f h : Nat)
    (different : h ≠ f) :
    accepts ⟨[], .star, [f]⟩ [h] = true := by
  simp [accepts, dropHead, admits, different]
  rfl

end BoundedMayPartition

#print axioms BoundedMayPartition.accepts_below
#print axioms BoundedMayPartition.partition_covers_every_point
#print axioms BoundedMayPartition.partition_query_count
#print axioms BoundedMayPartition.partition_path_bound
#print axioms BoundedMayPartition.partition_has_only_exact_or_star
#print axioms BoundedMayPartition.partition_preserves_every_point_witness
#print axioms BoundedMayPartition.partition_preserves_and_reflects_transfer
#print axioms BoundedMayPartition.split_includes_the_child_root
#print axioms BoundedMayPartition.a_guard_does_not_ban_an_unmentioned_field
