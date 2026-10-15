import Paper2.Paper1ProvedOddUnaryNRCanonicalJordan

/-! Normalize a genuine Jordan graph in its original coefficient field.
The trace, defect, and isotropic slope are computed from the retained
binary graph itself; no coefficient extension or new labels are used. -/
namespace Paper2.Paper1Proved.OddUnary.NRCanonical
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace JordanReceipt
variable {K : Type} [Field K] {r : ℕ} {b : ℕ → ℕ}
variable {H : (i : Fin r) → Holant.Signature K (b i.val)}
variable {phi : K →+* AlgebraicComplex}

def coefficient (J : JordanReceipt (H := H) phi) (i j : Bool) : K :=
  J.graph.network.denote ![i,j]

def eigenvalueK (J : JordanReceipt (H := H) phi) : K :=
  (J.coefficient false false+J.coefficient true true)/2

def defectK (J : JordanReceipt (H := H) phi) : K :=
  J.coefficient false false-J.eigenvalueK

def ratioK (J : JordanReceipt (H := H) phi) : K :=
  J.coefficient false true/J.defectK

theorem map_coefficient (J : JordanReceipt (H := H) phi) (i j : Bool) :
    phi (J.coefficient i j)=jordanMatrix J.eigenvalue J.defect J.repeated i j := by
  have h := congrFun J.form ![i,j]
  simpa only [coefficient,RingHomRealization.mapSignature,kernelSignature,
    Matrix.cons_val_zero,Matrix.cons_val_one] using h

theorem map_eigenvalueK (J : JordanReceipt (H := H) phi) :
    phi J.eigenvalueK=J.eigenvalue := by
  have trace : phi (J.coefficient false false)+phi (J.coefficient true true)=
      2*J.eigenvalue := by
    rw [J.map_coefficient,J.map_coefficient]
    simp only [jordanMatrix,ite_true]
    linear_combination J.defect*J.isotropic
  simp only [eigenvalueK,map_div₀,map_add,map_ofNat]
  rw [trace]
  ring

theorem map_defectK (J : JordanReceipt (H := H) phi) :
    phi J.defectK=J.defect*J.repeated false^2 := by
  simp only [defectK,map_sub,J.map_coefficient,J.map_eigenvalueK,jordanMatrix,ite_true]
  ring

theorem eigenvalueK_nonzero (J : JordanReceipt (H := H) phi) : J.eigenvalueK≠0 := by
  intro zero
  apply J.eigenvalueNonzero
  rw [←J.map_eigenvalueK,zero,map_zero]

theorem defectK_nonzero (J : JordanReceipt (H := H) phi) : J.defectK≠0 := by
  intro zero
  have mapped := J.map_defectK
  rw [zero,map_zero] at mapped
  exact (mul_ne_zero J.defectNonzero (pow_ne_zero _ J.repeatedFalseNonzero)) mapped.symm

theorem map_ratioK (J : JordanReceipt (H := H) phi) :
    phi J.ratioK=J.repeated true/J.repeated false := by
  simp only [ratioK,map_div₀,J.map_coefficient,J.map_defectK,jordanMatrix,
    Bool.false_eq_true,ite_false,zero_add]
  field_simp [J.defectNonzero,J.repeatedFalseNonzero]

theorem ratioK_square (J : JordanReceipt (H := H) phi)
    (injective : Function.Injective phi) : J.ratioK^2=-1 := by
  apply injective
  simp only [map_pow,map_neg,map_one,J.map_ratioK]
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 J.repeatedFalseNonzero)).mpr
  linear_combination J.isotropic

/-- The retained graph has a nonscalar Jordan kernel over the original
field, with its repeated vector normalized to `(1,t)`. -/
theorem original_form (J : JordanReceipt (H := H) phi)
    (injective : Function.Injective phi) :
    J.graph.network.denote=fun x =>
      (if x 0=x 1 then J.eigenvalueK else 0)+
        J.defectK*(if x 0 then J.ratioK else 1)*(if x 1 then J.ratioK else 1) := by
  funext x
  apply injective
  have h := congrFun J.form x
  change phi (J.graph.network.denote x)=jordanMatrix J.eigenvalue J.defect J.repeated (x 0) (x 1) at h
  rw [h]
  simp only [map_add,map_mul]
  cases x 0 <;> cases x 1 <;>
    simp only [jordanMatrix,ite_true,ite_false,Bool.false_eq_true,Bool.true_eq_false,
      map_zero,map_one,J.map_eigenvalueK,J.map_defectK,J.map_ratioK]
  all_goals field_simp [J.repeatedFalseNonzero]

end JordanReceipt
end
end Paper2.Paper1Proved.OddUnary.NRCanonical

