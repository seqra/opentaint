/- Only the ordinary execution publishes callbacks. The mask execution
   gives coordinate evidence that is intersected with each result. -/

def attachMask (member prior transported exact : Bool) : Bool :=
  (prior || ((transported && exact) || (transported && !exact))) && member

theorem wholeMaskOutput (member prior transported exact : Bool)
    (same : transported = member) :
    attachMask member prior transported exact = member := by
  subst transported
  cases member <;> cases prior <;> cases exact <;> rfl

theorem omitIdenticalMaskReplay {Coordinate : Type}
    (results prior duplicated exact : Coordinate → Bool)
    (sameGeometry : ∀ coordinate, duplicated coordinate = results coordinate) :
    ∀ coordinate,
      attachMask (results coordinate) (prior coordinate) (duplicated coordinate)
        (exact coordinate) = results coordinate := by
  intro coordinate
  exact wholeMaskOutput _ _ _ _ (sameGeometry coordinate)

theorem privateReplayPublishesNoRequests {Request : Type} (ordinary : List Request) :
    ([] : List Request) ++ ordinary = ordinary := rfl
