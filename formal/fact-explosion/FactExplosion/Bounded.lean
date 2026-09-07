import FactExplosion.Indexed

namespace FactExplosion

def boundedIntern
    (limit : Nat)
    (cache : List AccessTree)
    (tree : AccessTree) : List AccessTree × AccessTree :=
  match _found : locate tree cache with
  | some index => (cache, cache[index]?.getD tree)
  | none =>
      let retained := if cache.length ≥ limit then [] else cache
      (retained ++ [tree], tree)

def boundedInternFacts (limit : Nat) :
    List AccessTree → List AccessTree → List AccessTree × List AccessTree
  | cache, [] => (cache, [])
  | cache, tree :: tail =>
      let (nextCache, representative) := boundedIntern limit cache tree
      let (finalCache, representatives) := boundedInternFacts limit nextCache tail
      (finalCache, representative :: representatives)

theorem boundedIntern_value_exact
    (limit : Nat)
    (cache : List AccessTree)
    (tree : AccessTree) :
    (boundedIntern limit cache tree).2 = tree := by
  unfold boundedIntern
  split
  · rename_i index found
    have selected := locate_sound found
    simp [selected]
  · rfl

theorem boundedIntern_cache_bound
    {limit : Nat}
    (positive : 0 < limit)
    {cache : List AccessTree}
    (cacheBound : cache.length ≤ limit)
    (tree : AccessTree) :
    (boundedIntern limit cache tree).1.length ≤ limit := by
  unfold boundedIntern
  split
  · exact cacheBound
  · rename_i notFound
    split
    · simp
      exact positive
    · rename_i belowLimit
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

theorem boundedInternFacts_values_exact
    (limit : Nat)
    (cache facts : List AccessTree) :
    (boundedInternFacts limit cache facts).2 = facts := by
  induction facts generalizing cache with
  | nil => rfl
  | cons tree tail ih =>
      rw [boundedInternFacts]
      generalize internEqual : boundedIntern limit cache tree = step
      rcases step with ⟨nextCache, representative⟩
      have representativeExact : representative = tree := by
        have exact := boundedIntern_value_exact limit cache tree
        rw [internEqual] at exact
        exact exact
      generalize tailEqual : boundedInternFacts limit nextCache tail = result
      rcases result with ⟨finalCache, representatives⟩
      have representativesExact := ih nextCache
      rw [tailEqual] at representativesExact
      simp [tailEqual, representativeExact, representativesExact]

theorem boundedInternFacts_cache_bound
    {limit : Nat}
    (positive : 0 < limit)
    {cache : List AccessTree}
    (cacheBound : cache.length ≤ limit)
    (facts : List AccessTree) :
    (boundedInternFacts limit cache facts).1.length ≤ limit := by
  induction facts generalizing cache with
  | nil => exact cacheBound
  | cons tree tail ih =>
      rw [boundedInternFacts]
      generalize internEqual : boundedIntern limit cache tree = result
      rcases result with ⟨nextCache, representative⟩
      have nextBound := boundedIntern_cache_bound positive cacheBound tree
      rw [internEqual] at nextBound
      generalize tailEqual : boundedInternFacts limit nextCache tail = tailResult
      rcases tailResult with ⟨finalCache, representatives⟩
      have finalBound := ih nextBound
      rw [tailEqual] at finalBound
      simpa [internEqual, tailEqual] using finalBound

theorem boundedIntern_empty
    {limit : Nat}
    (positive : 0 < limit)
    (tree : AccessTree) :
    boundedIntern limit [] tree = ([tree], tree) := by
  have below : ¬0 ≥ limit := by omega
  simp [boundedIntern, locate, below]

theorem boundedIntern_hit (limit : Nat) (tree : AccessTree) :
    boundedIntern limit [tree] tree = ([tree], tree) := by
  unfold boundedIntern
  split
  · rename_i index found
    have selected := locate_sound found
    simp [selected]
  · rename_i notFound
    simp [locate] at notFound

theorem boundedInternFacts_repeated_existing
    (limit copies : Nat)
    (tree : AccessTree) :
    boundedInternFacts limit [tree] (List.replicate copies tree) =
      ([tree], List.replicate copies tree) := by
  induction copies with
  | zero => rfl
  | succ copies ih =>
      rw [List.replicate_succ]
      simp [boundedInternFacts, boundedIntern_hit, ih]

theorem boundedInternFacts_repeated
    {limit : Nat}
    (positive : 0 < limit)
    (copies : Nat)
    (tree : AccessTree) :
    boundedInternFacts limit [] (List.replicate (copies + 1) tree) =
      ([tree], List.replicate (copies + 1) tree) := by
  rw [List.replicate_succ]
  simp [boundedInternFacts, boundedIntern_empty positive,
    boundedInternFacts_repeated_existing]

end FactExplosion
