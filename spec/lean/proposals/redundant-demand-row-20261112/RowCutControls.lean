import RowCut

namespace RetainedDemandRowCut.Controls
open RetainedServiceBasis

def counted (_ : Nat) : Bool := true
def x : Row := ⟨0,1,2,.data,⟨.data,0,true,true,[7],.full 3,.exact,[]⟩,10⟩
def z : Row := ⟨1,1,2,.data,⟨.data,0,true,true,[7],.full 3,.star,[]⟩,20⟩
def y : Row := ⟨2,1,2,.data,⟨.data,0,true,true,[],.full 3,.may,[]⟩,10⟩
def sameQuery : Row := { x with nativeKey := 3, entry := { x.entry with tail := .star } }
def wrongOwner : Row := { sameQuery with owner := 2 }
def tooDeep : Row := { x with entry := { x.entry with path := [7,8] } }

theorem split_services_positive : checkCut counted [x,z,y] [z,y] = true := by decide
theorem no_c2_provider : checkCut counted [x,y] [y] = false := by decide
theorem no_c5_provider : checkCut counted [x,z] [z] = false := by decide
theorem wrong_owner_rejected : checkCut counted [x,wrongOwner] [wrongOwner] = false := by decide
theorem two_counted_fields_rejected : checkRow counted tooDeep [z,y] = false := by decide
theorem symmetric_singleton_one : checkCut counted [x,sameQuery] [x] = true := by decide
theorem symmetric_singleton_two : checkCut counted [x,sameQuery] [sameQuery] = true := by decide
theorem unsafe_joint_rejected : checkCut counted [x,sameQuery] [] = false := by decide
theorem duplicate_producer_is_not_provider : singletonKept [x,x] x = [] := by decide
theorem duplicate_producer_cut_rejected : checkCut counted [x,x] (singletonKept [x,x] x) = false := by decide
theorem nonexistent_provider_rejected : checkCut counted [x] [sameQuery] = false := by decide

#print axioms split_services_positive
#print axioms no_c2_provider
#print axioms no_c5_provider
#print axioms wrong_owner_rejected
#print axioms two_counted_fields_rejected
#print axioms symmetric_singleton_one
#print axioms symmetric_singleton_two
#print axioms unsafe_joint_rejected
#print axioms duplicate_producer_is_not_provider
#print axioms duplicate_producer_cut_rejected
#print axioms nonexistent_provider_rejected
end RetainedDemandRowCut.Controls
