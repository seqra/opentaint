import AuditReplySafety
import AuditNormalization
namespace AuditIntersection
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

abbrev contains := UniformActual.locationIn

theorem equal_heads_have_the_same_location_suffix (head a b : Path)
    (same : head++a=head++b) : a=b := List.append_cancel_left same

theorem exact_location_has_no_residual (a : Ap) (word : Path)
    (shape : a.tail=.exact) (inside : contains a word) : word=a.path := by
  rcases inside with ⟨rest,whereAt,allowed⟩
  cases rest with
  | nil => simpa using whereAt
  | cons f more => simp [admits,shape] at allowed

theorem root_exact_retains_the_selected_point (c : Value) (locEq : Path) :
    contains (exactAt c locEq).ap locEq := ⟨[],by simp [exactAt],by simp [exactAt,admits]⟩

theorem same_head_scalar_exit_loses_no_intersection_point
    (c : Value) (inputExit : Ap) (word : Path)
    (same : c.ap.path=(selector inputExit).path)
    (legal : (selector inputExit).tail≠.ne)
    (base : c.ap.base=(selector inputExit).base)
    (mark : marksMeet c.ap (selector inputExit)=true)
    (inC : contains c.ap word) (inD : contains (selector inputExit) word) :
    ∃ out,intersectExit c inputExit=some out ∧ contains out.ap word := by
  generalize dEq : selector inputExit=d at *
  have choose : (d.tail == .ne || c.ap.base != d.base || !marksMeet c.ap d)=false := by
    simp [legal,base,mark]
  have sameB : (c.ap.path==d.path)=true := by simpa using same
  cases ct : c.ap.tail
  case exact => exact ⟨c,by simp [intersectExit,dEq,choose,sameB,ct],inC⟩
  case star => exact ⟨c,by simp [intersectExit,dEq,choose,sameB,ct],inC⟩
  case ne =>
    have notExact : d.tail≠.exact := by
      intro dt
      have only := exact_location_has_no_residual d word dt inD
      rcases inC with ⟨rest,locEq,allowed⟩
      have empty : rest=[] := by rw [only,←same] at locEq; simpa using locEq.symm
      simp [ct,empty,admits] at allowed
    exact ⟨c,by simp [intersectExit,dEq,choose,sameB,ct,notExact],inC⟩
  case may =>
    by_cases dt : d.tail=.exact
    · have only := exact_location_has_no_residual d word dt inD
      exact ⟨exactAt c d.path,by simp only [intersectExit,dEq,choose,Bool.false_eq_true,ite_false,sameB,ite_true,ct]; simp [dt],by simpa [only] using root_exact_retains_the_selected_point c d.path⟩
    · exact ⟨c,by simp only [intersectExit,dEq,choose,Bool.false_eq_true,ite_false,sameB,ite_true,ct]; simp [dt],inC⟩
  case must =>
    by_cases dt : d.tail=.exact
    · have only := exact_location_has_no_residual d word dt inD
      exact ⟨exactAt c d.path,by simp only [intersectExit,dEq,choose,Bool.false_eq_true,ite_false,sameB,ite_true,ct]; simp [dt],by simpa [only] using root_exact_retains_the_selected_point c d.path⟩
    · by_cases star : d.tail=.star
      · refine ⟨{c with ap:={c.ap with e:=c.ap.e++d.e}},by simp only [intersectExit,dEq,choose,Bool.false_eq_true,ite_false,sameB,ite_true,ct]; simp [star],?_⟩
        rcases inC with ⟨rest,locEq,allowedC⟩
        rcases inD with ⟨restD,atD,allowedD⟩
        have restSame : rest=restD := by simpa [same] using locEq.symm.trans atD
        refine ⟨rest,locEq,?_⟩
        cases rest with
        | nil => simp [admits,ct]
        | cons f more =>
            subst restD
            simpa [admits,ct,star,List.contains_append] using And.intro allowedC allowedD
      · exact ⟨c,by simp only [intersectExit,dEq,choose,Bool.false_eq_true,ite_false,sameB,ite_true,ct]; simp [dt,star],inC⟩

theorem strip_common_path (head rest : Path) : dropHead head (head++rest)=some rest := by
  induction head with
  | nil => rfl
  | cons f more ih => simpa [dropHead] using ih

theorem a_proper_extension_is_not_its_prefix (head : Path) (field : Nat) (rest : Path) :
    head++(field::rest)≠head := by
  intro same
  have sizes := congrArg List.length same
  simp only [List.length_append,List.length_cons] at sizes
  omega

theorem deeper_candidate_scalar_exit_loses_no_intersection_point
    (c : Value) (inputExit : Ap) (word : Path) (field : Nat) (rest : Path)
    (deeper : c.ap.path=(selector inputExit).path++(field::rest))
    (legal : (selector inputExit).tail≠.ne)
    (base : c.ap.base=(selector inputExit).base)
    (mark : marksMeet c.ap (selector inputExit)=true)
    (inC : contains c.ap word) (inD : contains (selector inputExit) word) :
    ∃ out,intersectExit c inputExit=some out ∧ contains out.ap word := by
  generalize dEq : selector inputExit=d at *
  have keepC := inC
  have keepD := inD
  obtain ⟨suffixC,locC,_⟩ := inC
  obtain ⟨suffixD,locD,allowedD⟩ := inD
  have suffixSame : suffixD=(field::rest)++suffixC := by
    apply List.append_cancel_left (as:=d.path)
    calc
      d.path++suffixD=word := locD.symm
      _=c.ap.path++suffixC := locC
      _=d.path++((field::rest)++suffixC) := by rw [deeper,List.append_assoc]
  have firstOK : admits d.tail d.e (field::rest)=true := by
    simpa only [suffixSame,List.cons_append,admits] using allowedD
  have different : c.ap.path≠d.path := by rw [deeper];exact a_proper_extension_is_not_its_prefix _ _ _
  have differentB : (c.ap.path==d.path)=false := beq_eq_false_iff_ne.mpr different
  have strip : dropHead d.path c.ap.path=some (field::rest) := by rw [deeper];exact strip_common_path _ _
  have choose : (d.tail == .ne || c.ap.base != d.base || !marksMeet c.ap d)=false := by simp [legal,base,mark]
  exact ⟨c,by simp only [intersectExit,dEq,choose,Bool.false_eq_true,ite_false,differentB,strip,firstOK,ite_true],keepC⟩

theorem deeper_selector_scalar_exit_loses_no_intersection_point
    (c : Value) (inputExit : Ap) (word : Path) (field : Nat) (rest : Path)
    (deeper : (selector inputExit).path=c.ap.path++(field::rest))
    (legal : (selector inputExit).tail≠.ne)
    (base : c.ap.base=(selector inputExit).base)
    (mark : marksMeet c.ap (selector inputExit)=true)
    (inC : contains c.ap word) (inD : contains (selector inputExit) word) :
    ∃ out,intersectExit c inputExit=some out ∧ contains out.ap word := by
  generalize dEq : selector inputExit=d at *
  have keepC := inC
  have keepD := inD
  obtain ⟨suffixC,locC,allowedC⟩ := inC
  obtain ⟨suffixD,locD,allowedD⟩ := inD
  have suffixSame : suffixC=(field::rest)++suffixD := by
    apply List.append_cancel_left (as:=c.ap.path)
    calc
      c.ap.path++suffixC=word := locC.symm
      _=d.path++suffixD := locD
      _=c.ap.path++((field::rest)++suffixD) := by rw [deeper,List.append_assoc]
  have firstOK : admits c.ap.tail c.ap.e (field::rest)=true := by
    simpa only [suffixSame,List.cons_append,admits] using allowedC
  have different : c.ap.path≠d.path := by
    rw [deeper]
    exact Ne.symm (a_proper_extension_is_not_its_prefix _ _ _)
  have differentB : (c.ap.path==d.path)=false := beq_eq_false_iff_ne.mpr different
  have strip : dropHead c.ap.path d.path=some (field::rest) := by rw [deeper];exact strip_common_path _ _
  have noStrip : dropHead d.path c.ap.path=none := by
    rw [deeper]
    exact AuditNormalization.EXACT_before_normalization_cannot_execute_a_deeper_read _ _ _
  have choose : (d.tail == .ne || c.ap.base != d.base || !marksMeet c.ap d)=false := by simp [legal,base,mark]
  have dispatch : intersectExit c inputExit =
      if !admits c.ap.tail c.ap.e (field::rest) then none else
      match c.ap.tail with
      | .exact => none
      | .star => some c
      | .may | .ne => if d.tail == .exact then some (exactAt c d.path)
          else some {c with ap:={c.ap with path:=d.path,tail:=.may,e:=[]}}
      | .must => if d.tail == .exact then some (exactAt c d.path)
          else some {c with ap:={c.ap with path:=d.path,e:=if d.tail == .star then d.e else []}} := by
    simp only [intersectExit,dEq,choose,Bool.false_eq_true,ite_false,differentB,noStrip,strip]
    rfl
  simp only [firstOK,Bool.not_true,Bool.false_eq_true,ite_false] at dispatch
  cases ct : c.ap.tail
  case exact => simp [admits,ct] at firstOK
  case star => exact ⟨c,by simp [dispatch,ct],keepC⟩
  case may | ne =>
    by_cases dt : d.tail=.exact
    · have only := exact_location_has_no_residual d word dt keepD
      refine ⟨exactAt c d.path,by simp [dispatch,ct,dt],?_⟩
      simpa [only] using root_exact_retains_the_selected_point c d.path
    · exact ⟨{c with ap:={c.ap with path:=d.path,tail:=.may,e:=[]}},
        by simp [dispatch,ct,dt],⟨suffixD,locD,by cases suffixD <;> simp [admits]⟩⟩
  case must =>
    by_cases dt : d.tail=.exact
    · have only := exact_location_has_no_residual d word dt keepD
      refine ⟨exactAt c d.path,by simp [dispatch,ct,dt],?_⟩
      simpa [only] using root_exact_retains_the_selected_point c d.path
    · refine ⟨{c with ap:={c.ap with path:=d.path,e:=if d.tail == .star then d.e else []}},
        by simp [dispatch,ct,dt],⟨suffixD,locD,?_⟩⟩
      by_cases star : d.tail=.star
      · cases suffixD with
        | nil => simp [ct,admits]
        | cons f more => simpa [star,ct,admits] using allowedD
      · cases suffixD <;> simp [star,ct,admits]

theorem every_scalar_C5_exit_keeps_every_point_in_its_paired_intersection
    (c : Value) (inputExit : Ap) (word : Path)
    (legal : (selector inputExit).tail≠.ne)
    (base : c.ap.base=(selector inputExit).base)
    (mark : marksMeet c.ap (selector inputExit)=true)
    (inC : contains c.ap word) (inD : contains (selector inputExit) word) :
    ∃ out,intersectExit c inputExit=some out ∧ contains out.ap word := by
  have keepC := inC
  have keepD := inD
  obtain ⟨suffixC,locC,_⟩ := inC
  obtain ⟨suffixD,locD,_⟩ := inD
  rcases List.append_eq_append_iff.mp (locC.symm.trans locD) with
      ⟨extra,extension,_⟩ | ⟨extra,extension,_⟩
  · cases extra with
    | nil =>
        have same : c.ap.path=(selector inputExit).path := by simpa using extension.symm
        exact same_head_scalar_exit_loses_no_intersection_point c inputExit word same legal base mark keepC keepD
    | cons field rest =>
        exact deeper_selector_scalar_exit_loses_no_intersection_point c inputExit word field rest extension legal base mark keepC keepD
  · cases extra with
    | nil =>
        have same : c.ap.path=(selector inputExit).path := by simpa using extension
        exact same_head_scalar_exit_loses_no_intersection_point c inputExit word same legal base mark keepC keepD
    | cons field rest =>
        exact deeper_candidate_scalar_exit_loses_no_intersection_point c inputExit word field rest extension legal base mark keepC keepD

theorem cut_covers_every_original_point (budget : Nat) (c : Value) (word : Path)
    (inside : contains c.ap word) : contains (cut budget c).ap word := by
  by_cases beyond : budget<c.ap.path.length
  · rcases inside with ⟨suffix,located,_⟩
    have nonempty : c.ap.path.drop budget≠[] := by
      intro empty
      have sizes := congrArg List.length empty
      simp only [List.length_drop,List.length_nil] at sizes
      omega
    cases lost : c.ap.path.drop budget with
    | nil => exact False.elim (nonempty lost)
    | cons field rest =>
        have splitPath : c.ap.path=c.ap.path.take budget++(field::rest) := by
          rw [←lost]
          exact (List.take_append_drop budget c.ap.path).symm
        unfold cut
        rw [ite_eq_left beyond]
        refine ⟨(field::rest)++suffix,?_,by simp [admits]⟩
        change word=c.ap.path.take budget++((field::rest)++suffix)
        calc
          word=c.ap.path++suffix := located
          _=(c.ap.path.take budget++(field::rest))++suffix := congrArg (fun xs => xs++suffix) splitPath
          _=c.ap.path.take budget++((field::rest)++suffix) := List.append_assoc _ _ _
  · simpa [cut,beyond] using inside

theorem scalar_exit_preserves_mark_layer_and_literal_protection
    (c : Value) (d : Ap) (out : Value) (hit : intersectExit c d=some out) :
    out.ap.mark=c.ap.mark ∧ out.demand=c.demand ∧ out.h=c.h := by
  unfold intersectExit at hit
  dsimp only at hit
  cases ct : c.ap.tail <;> simp only [ct] at hit
  all_goals
    repeat' (split at hit)
    all_goals simp_all [exactAt]
    all_goals cases hit
    all_goals simp

end AuditIntersection
