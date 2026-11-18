import BbTrace

-- The native analyzer has loop blocks, but no general basic-block demand.
-- Check the later run using the compiled historical basic-block reference.
theorem run101StillHasDemand : AcyclicMayBbTrace.laterHandoffs 48 = true :=
  AcyclicMayBbTrace.arbitrarily_many_later_forward_handoffs_have_demand 48

#eval AcyclicMayBbTrace.laterHandoffs 48
#print axioms run101StillHasDemand
