import Paper2.Paper1ProvedOddUnaryNRJordanField
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Positive powers of the original-field Jordan kernel. Matrix products
here are ordinary Boolean-indexed matrix products, matching equality-edge
chains. All powers and pin images retain their exact scalar factors. -/
namespace Paper2.Paper1Proved.OddUnary.NRJordanPowers
open Holant Holant.Tractable
open scoped Matrix
noncomputable section
variable {K : Type} [Field K]

def repeated (t : K) : Bool → K := fun i => if i then t else 1

def nilpotent (t : K) : Matrix Bool Bool K :=
  Matrix.vecMulVec (repeated t) (repeated t)

def jordan (lambda defect t : K) : Matrix Bool Bool K :=
  lambda • 1+defect • nilpotent t

def pin (c : K) : Bool → K := fun i => if i then 0 else c

theorem nilpotent_square_value (t : K) :
    nilpotent t*nilpotent t=(1+t^2) • nilpotent t := by
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.mul_apply,Fintype.sum_bool,nilpotent,Matrix.vecMulVec_apply,
      repeated,Bool.false_eq_true,ite_true,ite_false,Matrix.smul_apply,smul_eq_mul]
  all_goals ring

theorem nilpotent_square (t : K) (isotropic : t^2=-1) :
    nilpotent t*nilpotent t=0 := by
  rw [nilpotent_square_value,isotropic]
  simp

theorem nilpotent_rank_one (t : K) : (nilpotent t).rank=1 := by
  apply Nat.le_antisymm
  · exact Matrix.rank_vecMulVec_le (repeated t) (repeated t)
  · have submatrix : (nilpotent t).submatrix (fun _ : Unit => false)
        (fun _ : Unit => false)=(1 : Matrix Unit Unit K) := by
      ext i j
      cases i
      cases j
      simp [nilpotent,Matrix.vecMulVec_apply,repeated]
    have bound := Matrix.rank_submatrix_le (nilpotent t)
      (fun _ : Unit => false) (fun _ : Unit => false)
    rw [submatrix,Matrix.rank_one] at bound
    simpa using bound

theorem repeated_true_nonzero (t : K) (isotropic : t^2=-1) : t≠0 := by
  intro zero
  simp [zero] at isotropic

theorem nilpotent_nonscalar (t : K) (isotropic : t^2=-1) (c : K) :
    nilpotent t≠c • (1 : Matrix Bool Bool K) := by
  intro equal
  have entry := congrFun (congrFun equal false) true
  apply repeated_true_nonzero t isotropic
  simpa [nilpotent,Matrix.vecMulVec_apply,repeated] using entry

theorem jordan_nonscalar (lambda defect t : K) (isotropic : t^2=-1)
    (defectNonzero : defect≠0) (c : K) : jordan lambda defect t≠c • 1 := by
  intro equal
  have entry := congrFun (congrFun equal false) true
  have product : defect*t=0 := by
    simpa [jordan,nilpotent,Matrix.vecMulVec_apply,repeated] using entry
  exact (mul_ne_zero defectNonzero (repeated_true_nonzero t isotropic)) product

/-- The positive exponent avoids a predecessor convention at zero. -/
theorem jordan_positive_power (lambda defect t : K) (isotropic : t^2=-1) (m : ℕ) :
    jordan lambda defect t^(m+1)=
      lambda^m • (lambda • (1 : Matrix Bool Bool K)+(((m+1 : ℕ) : K)*defect) • nilpotent t) := by
  induction m with
  | zero => simp [jordan]
  | succ m ih =>
    rw [pow_succ,ih]
    simp only [jordan,Matrix.smul_mul,add_mul,mul_add,Matrix.mul_smul,
      one_mul,mul_one,nilpotent_square t isotropic,smul_zero,add_zero,
      smul_smul,smul_add]
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,pow_succ,
      Nat.cast_add,Nat.cast_one]
    ring

theorem nilpotent_pin_image (t c : K) :
    nilpotent t *ᵥ pin c=c • repeated t := by
  ext i
  cases i <;>
    simp [Matrix.mulVec,dotProduct,nilpotent,Matrix.vecMulVec_apply,
      repeated,pin,mul_comm]

/-- The exact unary delivered by a positive-length equality-edge chain. -/
theorem jordan_positive_power_pin (lambda defect t : K) (isotropic : t^2=-1)
    (m : ℕ) (c : K) :
    jordan lambda defect t^(m+1) *ᵥ pin c=
      (lambda^(m+1)*c) • pin (1 : K)+
        (((m+1 : ℕ) : K)*lambda^m*defect*c) • repeated t := by
  rw [jordan_positive_power lambda defect t isotropic m]
  simp only [Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.one_mulVec,
    nilpotent_pin_image,smul_smul,smul_add]
  ext i
  cases i <;> simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,pin,repeated,
    Bool.false_eq_true,ite_true,ite_false,pow_succ]
  all_goals ring

section Receipt
variable {r : ℕ} {a : ℕ → ℕ}
variable {H : (i : Fin r) → Holant.Signature K (a i.val)}
variable {phi : K →+* AlgebraicComplex}

def receiptMatrix (J : NRCanonical.JordanReceipt (H := H) phi) : Matrix Bool Bool K :=
  fun i j => J.coefficient i j

theorem receiptMatrix_eq (J : NRCanonical.JordanReceipt (H := H) phi)
    (injective : Function.Injective phi) :
    receiptMatrix J=jordan J.eigenvalueK J.defectK J.ratioK := by
  ext i j
  have entry := congrFun (J.original_form injective) ![i,j]
  cases i <;> cases j <;>
    simpa [receiptMatrix,jordan,nilpotent,Matrix.vecMulVec_apply,repeated,
      NRCanonical.JordanReceipt.coefficient,mul_assoc] using entry

theorem receipt_positive_power (J : NRCanonical.JordanReceipt (H := H) phi)
    (injective : Function.Injective phi) (m : ℕ) :
    receiptMatrix J^(m+1)=J.eigenvalueK^m •
      (J.eigenvalueK • (1 : Matrix Bool Bool K)+
        (((m+1 : ℕ) : K)*J.defectK) • nilpotent J.ratioK) := by
  rw [receiptMatrix_eq J injective]
  exact jordan_positive_power _ _ _ (J.ratioK_square injective) m

theorem receipt_positive_power_pin (J : NRCanonical.JordanReceipt (H := H) phi)
    (injective : Function.Injective phi) (m : ℕ) (c : K) :
    receiptMatrix J^(m+1) *ᵥ pin c=
      (J.eigenvalueK^(m+1)*c) • pin (1 : K)+
        (((m+1 : ℕ) : K)*J.eigenvalueK^m*J.defectK*c) • repeated J.ratioK := by
  rw [receiptMatrix_eq J injective]
  exact jordan_positive_power_pin _ _ _ (J.ratioK_square injective) m c
end Receipt

end
end Paper2.Paper1Proved.OddUnary.NRJordanPowers

