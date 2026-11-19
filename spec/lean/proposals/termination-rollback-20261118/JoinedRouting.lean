/- The synchronous route audit needs one bit per runner. True means an
   accepted non-start event was posted to that runner. -/

def firstData (seen accepted isStart : Bool) : Bool :=
  if seen then true else accepted && !isStart

def recordPosts (seen : Bool) (posts : List (Bool × Bool)) : Bool :=
  posts.foldl (fun flag event => firstData flag event.1 event.2) seen

theorem firstData_retains_observation (seen accepted isStart : Bool) :
    firstData seen accepted isStart = (seen || (accepted && !isStart)) := by
  cases seen <;> rfl

theorem recordPosts_matches_all_accepted (seen : Bool) (posts : List (Bool × Bool)) :
    recordPosts seen posts = (seen || posts.any (fun event => event.1 && !event.2)) := by
  induction posts generalizing seen with
  | nil => cases seen <;> rfl
  | cons head tail ih =>
    change recordPosts (firstData seen head.1 head.2) tail =
      (seen || ((head.1 && !head.2) || tail.any (fun event => event.1 && !event.2)))
    rw [ih, firstData_retains_observation, Bool.or_assoc]

theorem recordPosts_rejects_foreign_service (posts : List (Bool × Bool))
    (silent : recordPosts false posts = false) :
    ∀ event ∈ posts, event.1 = true → event.2 = true := by
  intro event present accepted
  have empty : (posts.any (fun e => e.1 && !e.2)) = false := by
    simpa [recordPosts_matches_all_accepted] using silent
  cases h : event.2
  · have evidence : (event.1 && !event.2) = true := by simp [accepted, h]
    have observed : (posts.any (fun e => e.1 && !e.2)) = true :=
      List.any_eq_true.mpr ⟨event, present, evidence⟩
    rw [empty] at observed
    contradiction
  · rfl
