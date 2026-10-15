import Paper2.Certificates.BellClosures
import Paper2.NetworkRealization

/-! The closure queries of Q8.32/Q8.34 are literal finite native-X networks.
They keep every original vertex and add exactly two native edges. -/
namespace Paper2.Bell.Closures

variable {K : Type*} [CommRing K]

def cross13 : Equiv.Perm (Fin 4) where
  toFun := ![0,2,1,3]
  invFun := ![0,2,1,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def cross14 : Equiv.Perm (Fin 4) where
  toFun := ![0,2,3,1]
  invFun := ![0,3,1,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def close12 (N : Network K 4) : Network K 0 :=
  (N.contract Signature.disequality).contract Signature.disequality

def close13 (N : Network K 4) : Network K 0 := close12 (N.reindexBoundary cross13)
def close14 (N : Network K 4) : Network K 0 := close12 (N.reindexBoundary cross14)

theorem double_contract (H : Signature K 4) :
    Signature.contract Signature.disequality (Signature.contract Signature.disequality H) Fin.elim0 =
      native12 H := by
  simp only [Signature.contract,native12,fourPair,sum_word_succ,sum_word_zero,Fintype.sum_bool,
    Fin.cons_zero,Fin.cons_one,cons_two,cons_three]
  simp only [X_eq_disequality,Signature.disequality,ite_true,Bool.false_eq_true,Bool.true_eq_false,
    ite_false,zero_mul,one_mul,mul_zero,mul_one,add_zero,zero_add]
  ring

theorem native12_cross13 (H : Signature K 4) :
    native12 (Tensor.reindex cross13 H) = native13 H := by
  unfold native12 native13 fourPair
  apply Fintype.sum_equiv (Equiv.arrowCongr cross13.symm (Equiv.refl Bool))
  intro x
  rfl

theorem native12_cross14 (H : Signature K 4) :
    native12 (Tensor.reindex cross14 H) = native14 H := by
  unfold native12 native14 fourPair
  apply Fintype.sum_equiv (Equiv.arrowCongr cross14.symm (Equiv.refl Bool))
  intro x
  rfl

theorem denote_close12 (N : Network K 4) : (close12 N).denote Fin.elim0 = native12 N.denote := by
  unfold close12
  rw [Network.denote_contract,Network.denote_contract]
  exact double_contract N.denote

theorem denote_close13 (N : Network K 4) : (close13 N).denote Fin.elim0 = native13 N.denote := by
  rw [close13,denote_close12,Network.denote_reindexBoundary,native12_cross13]

theorem denote_close14 (N : Network K 4) : (close14 N).denote Fin.elim0 = native14 N.denote := by
  rw [close14,denote_close12,Network.denote_reindexBoundary,native12_cross14]

theorem closure_sizes (N : Network K 4) :
    (close12 N).shape.vertices = N.shape.vertices ∧
    (close13 N).shape.vertices = N.shape.vertices ∧
    (close14 N).shape.vertices = N.shape.vertices ∧
    (close12 N).shape.edges = N.shape.edges + 2 ∧
    (close13 N).shape.edges = N.shape.edges + 2 ∧
    (close14 N).shape.edges = N.shape.edges + 2 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem closure_uses (N : Network K 4) (F : SignatureFamily K) (h : N.Uses F) :
    (close12 N).Uses F ∧ (close13 N).Uses F ∧ (close14 N).Uses F := by
  exact ⟨(h.contract _).contract _,((h.reindexBoundary _).contract _).contract _,
    ((h.reindexBoundary _).contract _).contract _⟩

theorem closure_native (N : Network K 4) (h : N.NativeX) :
    (close12 N).NativeX ∧ (close13 N).NativeX ∧ (close14 N).NativeX := by
  exact ⟨h.contract.contract,(h.reindexBoundary _).contract.contract,
    (h.reindexBoundary _).contract.contract⟩

/-- Two actual closed graph queries, with their exact subtraction coefficient. -/
theorem two_y_network_queries (N : Network K 4) :
    fourPair N.denote Y Y = (close14 N).denote Fin.elim0 - (close13 N).denote Fin.elim0 := by
  rw [denote_close14,denote_close13,two_y_queries]

/-- Three actual closed graph queries for the EO I-pairing. -/
theorem two_i_network_queries (N : Network K 4)
    (hEO : ∀ x, (x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat ≠ 2 → N.denote x = 0) :
    (2 : K) * fourPair N.denote I I = (close13 N).denote Fin.elim0 +
      (close14 N).denote Fin.elim0 - (close12 N).denote Fin.elim0 := by
  rw [denote_close13,denote_close14,denote_close12]
  exact two_i_queries N.denote hEO

end Paper2.Bell.Closures
