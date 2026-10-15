import Paper2.DegreeCSP.ClassesToTract

/-! A single literal nonzero unary gauge on all original coordinates gives one
shared diagonal affine chart. Its scalar is retained at every arity, including
zero; no support or coefficient is replaced by an indicator. -/
namespace Paper2.DegreeCSP.MixedGaugeToTract
open scoped BigOperators
open Tractable
open Paper1Proved.OddUnary.GeneralizedEqualityNormalize
noncomputable section
set_option backward.isDefEq.respectTransparency false

def gauge {n : ℕ} (a b : AlgebraicComplex) (t : ℕ)
    (f : Signature AlgebraicComplex n) : Signature AlgebraicComplex n :=
  fun x => f x * ∏ i, (if x i then b else a) ^ t

def chart (a b : AlgebraicComplex) (t : ℕ) : AlgebraicComplex := (a / b) ^ t

theorem chart_ne_zero {a b : AlgebraicComplex} (ha : a ≠ 0) (hb : b ≠ 0)
    (t : ℕ) : chart a b t ≠ 0 := pow_ne_zero t (div_ne_zero ha hb)

theorem coordinate_factor {a b : AlgebraicComplex} (hb : b ≠ 0) (t : ℕ)
    (x : Bool) :
    (if x then 1 else chart a b t) = (b ^ t)⁻¹ * (if x then b else a) ^ t := by
  cases x
  · simpa [chart, div_eq_mul_inv, mul_pow] using
      (mul_comm (a ^ t) ((b ^ t)⁻¹))
  · simp [pow_ne_zero t hb]

theorem diagonal_gauge {n : ℕ} {a b : AlgebraicComplex}
    (ha : a ≠ 0) (hb : b ≠ 0) (t : ℕ) (f : Signature AlgebraicComplex n) :
    (diagonal (chart a b t) (chart_ne_zero ha hb t)).action f =
      fun x => ((b ^ t)⁻¹) ^ n * gauge a b t f x := by
  change Signature.coordinateAction (fun _ => diagonalKernel (chart a b t) 1) f = _
  rw [coordinateAction_diagonal]
  funext x
  have hc : diagonalCoefficient (chart a b t) 1 x =
      ((b ^ t)⁻¹) ^ n * ∏ i, (if x i then b else a) ^ t := by
    unfold diagonalCoefficient
    simp_rw [coordinate_factor hb]
    rw [Finset.prod_mul_distrib]
    simp
  rw [hc]
  unfold gauge
  ring

theorem affine_diagonal_of_gauge {n : ℕ} {a b : AlgebraicComplex}
    (ha : a ≠ 0) (hb : b ≠ 0) (t : ℕ) (f : Signature AlgebraicComplex n)
    (hf : Affine (gauge a b t f)) :
    Affine ((diagonal (chart a b t) (chart_ne_zero ha hb t)).action f) := by
  rw [diagonal_gauge ha hb t f]
  exact hf.scale (((b ^ t)⁻¹) ^ n)

theorem shared_diagonal_affine (F : SignatureFamily AlgebraicComplex)
    {a b : AlgebraicComplex} (ha : a ≠ 0) (hb : b ≠ 0) (t : ℕ)
    (hf : ∀ f ∈ F, Affine (gauge a b t f.2)) :
    ClassesToTract.SharedDiagonalAffine F := by
  refine ⟨chart a b t, chart_ne_zero ha hb t, ?_⟩
  intro f hmem
  exact affine_diagonal_of_gauge ha hb t f.2 (hf f hmem)

theorem tract_family (F : SignatureFamily AlgebraicComplex) (hfin : F.Finite)
    {a b : AlgebraicComplex} (ha : a ≠ 0) (hb : b ≠ 0) (t : ℕ)
    (hf : ∀ f ∈ F, Affine (gauge a b t f.2)) :
    Tract (familyAction sourceKBasis F) :=
  ClassesToTract.diagonal_affine_family F hfin (shared_diagonal_affine F ha hb t hf)

end
end Paper2.DegreeCSP.MixedGaugeToTract
