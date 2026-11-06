import DirectedAlias.Impl.CfgSound

/-!
# Liveness and kills

A kill makes a dead variable unassigned. `kill_sim` proves: if the liveness certificate holds
(`LiveOK`, the FIXED rule), and each kill of `g'` removes a variable that is not live at its node
(`KillOK`), then each execution of the CFG `g` without kills has an execution of the CFG `g'`
with kills with the same node, the same heap, the same counters, the same null tags, and the same
values of the live variables (`Agree`). So each value alias of live variables, and of heap
paths from them, is kept (`Agree.alias`), and the analysis of `g'` is sound for queries on
live variables of `g` (`csoundKill`).

THE RULE OF THE BRIEF IS UNSOUND (`LiveOKSpec`, see `Impl/CfgExamples.lean`): it removes the
written variables also from the live variables of the HANDLERS, but an exception happens
before the write. The fixed rule (`LiveOK`) adds all live variables of each handler.
-/

namespace DirectedAlias.Impl.Cfg

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly
open DirectedAlias.Sound.ValueSem DirectedAlias.Opt

variable {src : Nat → Obj × Cell} {statics : List Root}

/-! ## Agreement on the live variables -/

/-- Two instrumented states agree on `L`: the same heap, counters, null tags of the cells and
null counters, and the same values of the variables of `L`. -/
def Agree (L : List Var) (vs1 vs2 : VState) : Prop :=
  vs2.cs.heap = vs1.cs.heap ∧ vs2.cs.cnt = vs1.cs.cnt ∧ vs2.nh = vs1.nh ∧ vs2.nc = vs1.nc ∧
    ∀ x ∈ L, vs2.val x = vs1.val x

/-- A state agrees with itself. -/
theorem Agree.refl (L : List Var) (vs : VState) : Agree L vs vs :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Agreement on `L` gives agreement on a subset. -/
theorem Agree.mono {L M : List Var} {vs1 vs2 : VState} (h : Agree L vs1 vs2)
    (hm : ∀ x ∈ M, x ∈ L) : Agree M vs1 vs2 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun x hx => h.2.2.2.2 x (hm x hx)⟩

/-- The value of a variable depends only on its foundation value and its null tag. -/
theorem val_congr {vs vs' : VState} {y : Var} (he : vs'.cs.env y = vs.cs.env y)
    (hn : vs'.nv y = vs.nv y) : vs'.val y = vs.val y := by
  unfold VState.val; rw [he, hn]

/-- A variable that holds an object has the object as its value. -/
theorem val_some {vs : VState} {y : Var} {o : Obj} (h : vs.cs.env y = some o) :
    vs.val y = some (.obj o) := by
  unfold VState.val; rw [h]

/-- The same value gives the same foundation value. -/
theorem env_of_val {vs vs' : VState} {y : Var} (h : vs'.val y = vs.val y) :
    vs'.cs.env y = vs.cs.env y := by
  unfold VState.val at h
  cases e1 : vs'.cs.env y with
  | some o1 =>
    cases e2 : vs.cs.env y with
    | some o2 => rw [e1, e2] at h; cases h; rfl
    | none =>
      rw [e1, e2] at h
      cases e3 : vs.nv y with
      | none => rw [e3] at h; cases h
      | some t => rw [e3] at h; cases h
  | none =>
    cases e2 : vs.cs.env y with
    | none => rfl
    | some o2 =>
      rw [e1, e2] at h
      cases e3 : vs'.nv y with
      | none => rw [e3] at h; cases h
      | some t => rw [e3] at h; cases h

/-- Agreeing states give the same foundation value of an agreeing variable. -/
theorem Agree.env' {L : List Var} {vs1 vs2 : VState} (h : Agree L vs1 vs2) {y : Var}
    (hy : y ∈ L) : vs2.cs.env y = vs1.cs.env y :=
  env_of_val (h.2.2.2.2 y hy)

/-- Agreeing states give the same object of an agreeing variable. -/
theorem Agree.env {L : List Var} {vs1 vs2 : VState} (h : Agree L vs1 vs2) {y : Var}
    (hy : y ∈ L) {o : Obj} (he : vs1.cs.env y = some o) : vs2.cs.env y = some o :=
  val_obj ((h.2.2.2.2 y hy).trans (val_some he))

/-- Agreeing states give the same value of each cell. -/
theorem Agree.cell {L : List Var} {vs1 vs2 : VState} (h : Agree L vs1 vs2) (o : Obj) (c : Cell) :
    vs2.cell o c = vs1.cell o c := by
  unfold VState.cell; rw [h.1, h.2.2.1]

/-- The value of the set variable after `setVarV`. -/
theorem val_setVarV_same (vs : VState) (x : Var) (v : VVal) : (vs.setVarV x v).val x = some v := by
  cases v with
  | obj o => exact val_some (fupd_same _ _ _)
  | nul t =>
    show (match fupd vs.cs.env x none x with
      | some o => some (VVal.obj o) | none => (fupd vs.nv x (some t) x).map VVal.nul) = _
    rw [fupd_same, fupd_same]; rfl

/-- The value of another variable after `setVarV`. -/
theorem val_setVarV_ne (vs : VState) {x y : Var} (v : VVal) (h : y ≠ x) :
    (vs.setVarV x v).val y = vs.val y := by
  cases v with
  | obj o => exact val_congr (fupd_ne _ _ h) rfl
  | nul t => exact val_congr (fupd_ne _ _ h) (fupd_ne _ _ h)

/-- The heap after `setVarV`. -/
theorem setVarV_heap (vs : VState) (x : Var) (v : VVal) : (vs.setVarV x v).cs.heap = vs.cs.heap := by
  rw [setVarV_cs]; rfl

/-- The counters after `setVarV`. -/
theorem setVarV_cnt (vs : VState) (x : Var) (v : VVal) : (vs.setVarV x v).cs.cnt = vs.cs.cnt := by
  rw [setVarV_cs]; rfl

/-- The null tags of the cells after `setVarV`. -/
theorem setVarV_nh (vs : VState) (x : Var) (v : VVal) : (vs.setVarV x v).nh = vs.nh := by
  cases v <;> rfl

/-- The null counters after `setVarV`. -/
theorem setVarV_nc (vs : VState) (x : Var) (v : VVal) : (vs.setVarV x v).nc = vs.nc := by
  cases v <;> rfl

/-- The values after `setCellV`. -/
theorem setCellV_val (vs : VState) (o : Obj) (c : Cell) (v : VVal) (y : Var) :
    (vs.setCellV o c v).val y = vs.val y := by
  cases v <;> rfl

/-- `setVarV` on agreeing states. -/
theorem Agree.setVarV {L : List Var} {vs1 vs2 : VState} (h : Agree L vs1 vs2) (x : Var) (v : VVal) :
    ∀ M : List Var, (∀ y ∈ M, y ∉ [x] → y ∈ L) → Agree M (vs1.setVarV x v) (vs2.setVarV x v) := by
  intro M hM
  refine ⟨by rw [setVarV_heap, setVarV_heap, h.1], by rw [setVarV_cnt, setVarV_cnt, h.2.1],
    by rw [setVarV_nh, setVarV_nh, h.2.2.1], by rw [setVarV_nc, setVarV_nc, h.2.2.2.1],
    fun y hy => ?_⟩
  by_cases e : y = x
  · subst e; rw [val_setVarV_same, val_setVarV_same]
  · rw [val_setVarV_ne _ _ e, val_setVarV_ne _ _ e]
    exact h.2.2.2.2 y (hM y hy (fun hm => e (List.mem_singleton.mp hm)))

/-- A new symbolic or allocated object in a variable, with a counter bump, on agreeing states. -/
theorem Agree.setBump {L : List Var} {vs1 vs2 : VState} (h : Agree L vs1 vs2) (x : Var) (o : Obj)
    (s : Site) : ∀ M : List Var, (∀ y ∈ M, y ∉ [x] → y ∈ L) →
      Agree M { vs1 with cs := (vs1.cs.setVar x (some o)).bump s }
        { vs2 with cs := (vs2.cs.setVar x (some o)).bump s } := by
  intro M hM
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2.1, fun y hy => ?_⟩
  · show fupd vs2.cs.cnt s (vs2.cs.cnt s + 1) = fupd vs1.cs.cnt s (vs1.cs.cnt s + 1)
    rw [h.2.1]
  · by_cases e : y = x
    · subst e
      exact (val_some (vs := { vs2 with cs := (vs2.cs.setVar y (some o)).bump s })
        (fupd_same _ _ _)).trans (val_some (fupd_same _ _ _)).symm
    · have h2 := h.2.2.2.2 y (hM y hy (fun hm => e (List.mem_singleton.mp hm)))
      have e1 : ({ vs2 with cs := (vs2.cs.setVar x (some o)).bump s } : VState).val y =
          vs2.val y := val_congr (fupd_ne _ _ e) rfl
      have e2 : ({ vs1 with cs := (vs1.cs.setVar x (some o)).bump s } : VState).val y =
          vs1.val y := val_congr (fupd_ne _ _ e) rfl
      rw [e1, e2]; exact h2

/-- `setCellV` on agreeing states. -/
theorem Agree.setCellV {L : List Var} {vs1 vs2 : VState} (h : Agree L vs1 vs2) (o : Obj) (c : Cell)
    (v : VVal) : ∀ M : List Var, (∀ y ∈ M, y ∉ ([] : List Var) → y ∈ L) →
      Agree M (vs1.setCellV o c v) (vs2.setCellV o c v) := by
  intro M hM
  refine ⟨by rw [setCellV_heap, setCellV_heap, h.1], ?_, ?_, ?_, fun y hy => ?_⟩
  · rw [setCellV_cs, setCellV_cs]; exact h.2.1
  · cases v with
    | obj _ => exact h.2.2.1
    | nul t => show fupd2 vs2.nh o c t = fupd2 vs1.nh o c t; rw [h.2.2.1]
  · cases v <;> exact h.2.2.2.1
  · rw [setCellV_val, setCellV_val]; exact h.2.2.2.2 y (hM y hy (fun hm => nomatch hm))

/-- Narrow reach depends only on the arguments and the heap. -/
theorem ReachN_congr {st1 st2 : CState} {args : List Var}
    (he : ∀ x ∈ args, st2.env x = st1.env x) (hh : st2.heap = st1.heap) {o : Obj}
    (h : ReachN st1 statics args o) : ReachN st2 statics args o := by
  induction h with
  | arg hx he' => exact .arg hx ((he _ hx).trans he')
  | static hr => exact .static hr
  | step _ hc ih => exact .step ih (hh ▸ hc)

/-! ## Steps on agreeing states -/

/-- An instrumented statement step on agreeing states: the second state makes the same step,
and the results agree on each set whose variables are written or agree. -/
theorem sstep_agree {i : Nat} {st : Stmt} {L : List Var} {vs1 vs2 vs1' : VState}
    (ha : Agree L vs1 vs2) (hu : ∀ x ∈ st.uses, x ∈ L) (h : SStepV src statics i st vs1 vs1') :
    ∃ vs2', SStepV src statics i st vs2 vs2' ∧
      ∀ M : List Var, (∀ y ∈ M, y ∉ st.defs → y ∈ L) → Agree M vs1' vs2' := by
  cases h with
  | @new x s _ =>
    refine ⟨_, .new, ?_⟩
    rw [ha.2.1]; exact ha.setBump x _ s
  | @null x _ =>
    refine ⟨_, .null, fun M hM => ?_⟩
    have := ha.setVarV x (.nul (.site i (vs1.nc i))) M hM
    rw [ha.2.2.2.1]
    exact ⟨this.1, this.2.1, this.2.2.1, rfl, this.2.2.2.2⟩
  | @copy x y _ v hv =>
    have hy : y ∈ L := hu y List.mem_cons_self
    exact ⟨_, .copy ((ha.2.2.2.2 y hy).trans hv), ha.setVarV x v⟩
  | @load x y f _ o he =>
    have hy : y ∈ L := hu y List.mem_cons_self
    refine ⟨_, .load (ha.env hy he), ?_⟩
    rw [ha.cell]; exact ha.setVarV x _
  | @store x f y _ o v he hv =>
    have hx : x ∈ L := hu x List.mem_cons_self
    have hy : y ∈ L := hu y (List.mem_cons_of_mem _ List.mem_cons_self)
    exact ⟨_, .store (ha.env hx he) ((ha.2.2.2.2 y hy).trans hv), ha.setCellV o _ v⟩
  | @aload x y _ o j he =>
    have hy : y ∈ L := hu y List.mem_cons_self
    refine ⟨_, .aload j (ha.env hy he), ?_⟩
    rw [ha.cell]; exact ha.setVarV x _
  | @astore x y _ o v j he hv =>
    have hx : x ∈ L := hu x List.mem_cons_self
    have hy : y ∈ L := hu y (List.mem_cons_of_mem _ List.mem_cons_self)
    exact ⟨_, .astore j (ha.env hx he) ((ha.2.2.2.2 y hy).trans hv), ha.setCellV o _ v⟩
  | @unknown x s _ =>
    refine ⟨_, .unknown, ?_⟩
    rw [ha.2.1]; exact ha.setBump x _ s
  | @call ret s args _ h' hh =>
    have hh2 : HavocN src statics vs2.cs args s (vs2.cs.cnt s) h' := by
      intro o c
      rw [ha.2.1, ha.1]
      rcases hh o c with e | ⟨hr, k, hk, e⟩
      · exact Or.inl e
      · exact Or.inr ⟨ReachN_congr (fun x hx => ha.env' (hu x hx)) ha.1 hr, k, hk, e⟩
    refine ⟨_, .call hh2, fun M hM => ?_⟩
    rw [ha.2.1]
    have hH : ∀ st : CState,
        ((st.setRet ret (some (.sym (.fresh s (vs1.cs.cnt s)) []))).bump s).heap = st.heap :=
      fun st => by cases ret <;> rfl
    refine ⟨(hH { vs2.cs with heap := h' }).trans (hH { vs1.cs with heap := h' }).symm, ?_, ha.2.2.1, ha.2.2.2.1, fun y hy => ?_⟩
    · show fupd ({ vs2.cs with heap := h' }.setRet ret _).cnt s
          (({ vs2.cs with heap := h' }.setRet ret _).cnt s + 1) =
        fupd ({ vs1.cs with heap := h' }.setRet ret _).cnt s
          (({ vs1.cs with heap := h' }.setRet ret _).cnt s + 1)
      rw [setRet_cnt, setRet_cnt]
      show fupd vs2.cs.cnt s (vs2.cs.cnt s + 1) = fupd vs1.cs.cnt s (vs1.cs.cnt s + 1)
      rw [ha.2.1]
    · cases ret with
      | none =>
        have h2 := ha.2.2.2.2 y (hM y hy (fun hm => nomatch hm))
        exact (val_congr (vs := vs2) rfl rfl).trans (h2.trans (val_congr (vs := vs1) rfl rfl).symm)
      | some r =>
        by_cases e : y = r
        · subst e
          exact (val_some (fupd_same _ _ _)).trans (val_some (fupd_same _ _ _)).symm
        · have h2 := ha.2.2.2.2 y (hM y hy (fun hm => e (List.mem_singleton.mp hm)))
          have e1 : ({ vs2 with cs := ({ vs2.cs with heap := h' }.setRet (some r)
              (some (.sym (.fresh s (vs1.cs.cnt s)) []))).bump s } : VState).val y = vs2.val y :=
            val_congr (fupd_ne _ _ e) rfl
          have e2 : ({ vs1 with cs := ({ vs1.cs with heap := h' }.setRet (some r)
              (some (.sym (.fresh s (vs1.cs.cnt s)) []))).bump s } : VState).val y = vs1.val y :=
            val_congr (fupd_ne _ _ e) rfl
          rw [e1, e2]; exact h2

/-- A normal instruction step on agreeing states: the second state makes the same step, and the
results agree on each set whose variables are written or agree. -/
theorem istep_agree {i : Nat} {ins : Instr} {e : Option Obj} {L : List Var} {vs1 vs2 vs1' : VState}
    (ha : Agree L vs1 vs2) (hu : ∀ x ∈ ins.uses, x ∈ L) (h : IStep src statics i ins e vs1 vs1') :
    ∃ vs2', IStep src statics i ins e vs2 vs2' ∧
      ∀ M : List Var, (∀ y ∈ M, y ∉ ins.defs → y ∈ L) → Agree M vs1' vs2' := by
  cases h with
  | stmt h =>
    obtain ⟨vs2', h2, ha'⟩ := sstep_agree ha hu h
    exact ⟨vs2', .stmt h2, ha'⟩
  | nop => exact ⟨vs2, .nop, fun M hM => ha.mono (fun y hy => hM y hy (fun hm => nomatch hm))⟩
  | thr => exact ⟨vs2, .thr, fun M hM => ha.mono (fun y hy => hM y hy (fun hm => nomatch hm))⟩
  | @catP x s o _ => exact ⟨_, .catP, ha.setVarV x (.obj o)⟩
  | @catF x s _ _ h =>
    obtain ⟨vs2', h2, ha'⟩ := sstep_agree (st := .unknown x s) ha (fun _ hm => nomatch hm) h
    exact ⟨vs2', .catF h2, ha'⟩
  | @cnstF x s _ _ _ h =>
    obtain ⟨vs2', h2, ha'⟩ := sstep_agree (st := .unknown x s) ha (fun _ hm => nomatch hm) h
    exact ⟨vs2', .cnstF h2, ha'⟩
  | @cnstR x s _ _ n hn =>
    exact ⟨_, .cnstR (by rw [ha.2.1]; exact hn), ha.setVarV x _⟩

/-- An exceptional instruction step on agreeing states: the second state makes the same step,
and the results agree on the same set. -/
theorem xstep_agree {ins : Instr} {e' : Option Obj} {L : List Var} {vs1 vs2 vs1' : VState}
    (ha : Agree L vs1 vs2) (hu : ∀ x ∈ ins.uses, x ∈ L) (h : XStep src statics ins vs1 vs1' e') :
    ∃ vs2', XStep src statics ins vs2 vs2' e' ∧ Agree L vs1' vs2' := by
  cases h with
  | none => exact ⟨vs2, .none, ha⟩
  | @thr y _ o hy => exact ⟨vs2, .thr (ha.env (hu y List.mem_cons_self) hy), ha⟩
  | @call ret s args _ _ h =>
    obtain ⟨vs2', h2, ha'⟩ := sstep_agree (st := .call none s args) ha (fun x hx => hu x hx) h
    exact ⟨vs2', .call h2, ha' L (fun y hy _ => hy)⟩

/-- A kill of a variable outside `L` keeps the agreement on `L`. -/
theorem Agree.kill {L : List Var} {vs1 vs2 : VState} (h : Agree L vs1 vs2) {x : Var} (hx : x ∉ L) :
    Agree L vs1 (killV vs2 x) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun y hy => by
    have e : y ≠ x := fun e => hx (e ▸ hy)
    have e1 : (killV vs2 x).val y = vs2.val y := val_congr (fupd_ne _ _ e) (fupd_ne _ _ e)
    rw [e1]; exact h.2.2.2.2 y hy⟩

/-- Kills of variables outside `L` keep the agreement on `L`. -/
theorem Agree.killAll {L : List Var} : ∀ (xs : List Var) {vs1 vs2 : VState}, Agree L vs1 vs2 →
    (∀ x ∈ xs, x ∉ L) → Agree L vs1 (killAllV xs vs2)
  | [], _, _, h, _ => h
  | x :: xs, _, _, h, hx =>
    Agree.killAll xs (h.kill (hx x List.mem_cons_self)) (fun y hy => hx y (List.mem_cons_of_mem _ hy))

/-! ## The CFG with kills -/

/-- The node of `g'` at the index of a node of `g` has the same instruction and edges. -/
theorem KillExt.node {g g' : Cfg} (hk : KillExt g g') {v : Nat} {nd : Node}
    (hn : g.nodes[v]? = some nd) :
    ∃ nd', g'.nodes[v]? = some nd' ∧ nd'.instr = nd.instr ∧ nd'.succ = nd.succ ∧ nd'.exc = nd.exc := by
  have h1 : (g'.nodes.map Node.strip)[v]? = some nd.strip := by
    rw [hk.strip, List.getElem?_map, hn]; rfl
  rw [List.getElem?_map] at h1
  cases e : g'.nodes[v]? with
  | none => rw [e] at h1; cases h1
  | some nd' =>
    rw [e] at h1
    have h2 : nd'.strip = nd.strip := Option.some.inj h1
    have i1 : nd'.strip.instr = nd.strip.instr := congrArg (fun n : Node => n.instr) h2
    have i2 : nd'.strip.succ = nd.strip.succ := congrArg (fun n : Node => n.succ) h2
    have i3 : nd'.strip.exc = nd.strip.exc := congrArg (fun n : Node => n.exc) h2
    exact ⟨nd', rfl, i1, i2, i3⟩

/-- The null site of a node depends only on the nodes without their kills. -/
theorem nullSite_strip (g : Cfg) (v : Nat) :
    g.nullSite v = (((g.nodes.map Node.strip).map (fun nd => nd.instr.nullN)).take v).sum := by
  unfold Cfg.nullSite
  rw [List.map_map, List.map_take]
  rfl

/-- The CFG with kills has the null sites of the CFG without kills. -/
theorem KillExt.nullSite {g g' : Cfg} (hk : KillExt g g') (v : Nat) :
    g'.nullSite v = g.nullSite v := by
  rw [nullSite_strip, nullSite_strip, hk.strip]

/-- THE KILL SIMULATION: each execution of the CFG without kills has an execution of the CFG with
kills at the same node, with the same pending exception, and with a state that agrees on the
live variables of the node (same heap, counters and null tags). -/
theorem kill_sim {g g' : Cfg} {fr : Frame} {live : Nat → List Var} (hl : LiveOK g live)
    (hk : KillExt g g') (hko : KillOK g' live) {c : Conf} (hr : Reach src statics g fr c) :
    ∃ vs2, Reach src statics g' fr ⟨c.node, vs2, c.exc⟩ ∧ Agree (live c.node) c.vs vs2 := by
  induction hr with
  | init =>
    refine ⟨VState.init fr, ?_, Agree.refl _ _⟩
    have := Reach.init (src := src) (statics := statics) (g := g') (fr := fr)
    rw [hk.entry] at this
    exact this
  | @step c c' _ hs ih =>
    obtain ⟨vs2, hr2, ha⟩ := ih
    cases hs with
    | @norm v nd w vs vs' e hn hw hi =>
      obtain ⟨nd', hn', hins, hsucc, _⟩ := hk.node hn
      obtain ⟨hlu, hls, _⟩ := hl v nd hn
      have hk0 : killAllV nd.kills vs = vs := by rw [hk.noKill v nd hn]; rfl
      rw [hk0] at hi
      have ha2 := ha.killAll nd'.kills (hko v nd' hn')
      obtain ⟨vs2', hi2, ha'⟩ := istep_agree ha2 hlu hi
      refine ⟨vs2', .step hr2 (.norm hn' (hsucc ▸ hw) ?_), ha' _ (hls w hw)⟩
      rw [hins, hk.nullSite]; exact hi2
    | @exc v nd h vs vs' e e' hn hh hx =>
      obtain ⟨nd', hn', hins, _, hexc⟩ := hk.node hn
      obtain ⟨hlu, _, hle⟩ := hl v nd hn
      have hk0 : killAllV nd.kills vs = vs := by rw [hk.noKill v nd hn]; rfl
      rw [hk0] at hx
      have ha2 := ha.killAll nd'.kills (hko v nd' hn')
      obtain ⟨vs2', hx2, ha'⟩ := xstep_agree ha2 hlu hx
      refine ⟨vs2', .step hr2 (.exc hn' (hexc ▸ hh) ?_), ha'.mono (hle h hh)⟩
      rw [hins]; exact hx2

/-! ## Aliases of live variables -/

/-- Following a path depends only on the heap and the null tags of the cells. -/
theorem readV_congr {vs1 vs2 : VState} (hh : vs2.cs.heap = vs1.cs.heap) (hn : vs2.nh = vs1.nh) :
    ∀ (v : VVal) (p : List Cell), vs2.readV v p = vs1.readV v p
  | _, [] => rfl
  | .nul _, _ :: _ => rfl
  | .obj o, c :: cs => by
    show vs2.readV (vs2.cell o c) cs = vs1.readV (vs1.cell o c) cs
    have : vs2.cell o c = vs1.cell o c := by unfold VState.cell; rw [hh, hn]
    rw [this]; exact readV_congr hh hn _ cs

/-- Agreeing states give the same value of each access path from an agreeing variable. -/
theorem Agree.evalV {L : List Var} {vs1 vs2 : VState} (h : Agree L vs1 vs2) {x : Var} (hx : x ∈ L)
    (p : List Cell) : vs2.evalV x p = vs1.evalV x p := by
  unfold VState.evalV
  rw [h.2.2.2.2 x hx]
  cases vs1.val x with
  | none => rfl
  | some v => exact readV_congr h.1 h.2.2.1 v p

/-- THE KILLS KEEP THE ALIASES OF LIVE VARIABLES: a value alias of two agreeing variables (and of
heap paths from them) holds in each agreeing state. -/
theorem Agree.alias {L : List Var} {vs1 vs2 : VState} (h : Agree L vs1 vs2) {x y : Var}
    (hx : x ∈ L) (hy : y ∈ L) {px py : List Cell} (ha : AliasInV vs1 x px y py) :
    AliasInV vs2 x px y py := by
  obtain ⟨v, h1, h2⟩ := ha
  exact ⟨v, (h.evalV hx px).trans h1, (h.evalV hy py).trans h2⟩

/-- THE ANALYSIS WITH KILLS IS SOUND FOR LIVE QUERIES: a post-fixpoint of the CFG with kills
answers true for each value alias of live variables at a reachable node of the CFG without
kills. -/
theorem csoundKill {cb : CtxB} {g g' : Cfg} {fr : Frame} {guard : Origin → Bool}
    {Sb Sa : Nat → AState} {T : Nat → List Origin} {live : Nat → List Var}
    (hok : CfgOK cb g') (hpf : PostFix cb guard g' fr Sb Sa T) (hfr : FrameOK cb.cn.ctx fr)
    (hl : LiveOK g live) (hk : KillExt g g') (hko : KillOK g' live)
    {v : Nat} {vs : VState} {e : Option Obj} (hr : Reach src cb.cn.statics g fr ⟨v, vs, e⟩)
    {x y : Var} {px py : List Cell} (hx : x ∈ live v) (hy : y ∈ live v)
    (hcx : ∀ c ∈ px, c.abs ∈ cb.cn.ctx.cells) (hcy : ∀ c ∈ py, c.abs ∈ cb.cn.ctx.cells)
    (ha : AliasInV vs x px y py) : may (Sb v) x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  obtain ⟨vs2, hr2, hag⟩ := kill_sim hl hk hko hr
  exact csoundCfg_may hok hpf hfr hr2 hcx hcy (hag.alias hx hy ha)

/-- The Boolean liveness check gives the fixed liveness rule. -/
theorem liveOKB_sound {g : Cfg} {live : Nat → List Var} (h : liveOKB g live = true) :
    LiveOK g live := by
  intro v nd hn
  have h1 := List.all_eq_true.mp h v (List.mem_range.mpr (by
    by_cases hlt : v < g.nodes.length
    · exact hlt
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hn; cases hn))
  rw [hn] at h1
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨hu, hs⟩, he⟩ := h1
  refine ⟨subB_iff.mp hu, fun w hw x hx hd => ?_, fun h hh x hx => subB_iff.mp (he h hh) x hx⟩
  rcases hs w hw x hx with h2 | h2
  · exact absurd h2 hd
  · exact h2

/-- The Boolean check of the brief gives the liveness rule of the brief. -/
theorem liveOKSpecB_sound {g : Cfg} {live : Nat → List Var} (h : liveOKSpecB g live = true) :
    LiveOKSpec g live := by
  intro v nd hn
  have h1 := List.all_eq_true.mp h v (List.mem_range.mpr (by
    by_cases hlt : v < g.nodes.length
    · exact hlt
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hn; cases hn))
  rw [hn] at h1
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h1
  obtain ⟨hu, hs⟩ := h1
  refine ⟨subB_iff.mp hu, fun w hw x hx hd => ?_⟩
  rcases hs w hw x hx with h2 | h2
  · exact absurd h2 hd
  · exact h2

/-- The Boolean check of the kills: no kill of a node removes a live variable of the node. -/
def killOKB (g' : Cfg) (live : Nat → List Var) : Bool :=
  (List.range g'.nodes.length).all (fun v => match g'.nodes[v]? with
    | some nd => nd.kills.all (fun x => !decide (x ∈ live v))
    | none => true)

/-- The Boolean kill check gives `KillOK`. -/
theorem killOKB_sound {g' : Cfg} {live : Nat → List Var} (h : killOKB g' live = true) :
    KillOK g' live := by
  intro v nd hn x hx hl
  have h1 := List.all_eq_true.mp h v (List.mem_range.mpr (by
    by_cases hlt : v < g'.nodes.length
    · exact hlt
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hn; cases hn))
  rw [hn] at h1
  have h2 := List.all_eq_true.mp h1 x hx
  rw [decide_eq_true hl] at h2
  cases h2

/-- A CFG whose nodes have no kills satisfies the kill condition of `KillExt`. -/
theorem noKill_of_all {g : Cfg} (h : ∀ nd ∈ g.nodes, nd.kills = []) :
    ∀ (v : Nat) (nd : Node), g.nodes[v]? = some nd → nd.kills = [] :=
  fun _ _ hn => h _ (List.mem_of_getElem? hn)

end DirectedAlias.Impl.Cfg
