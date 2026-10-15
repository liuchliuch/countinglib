import Paper2.HeightOne.PhaseCards.Kernels

/-! Literal coefficient-ratio arithmetic in source Lemma 5.11. The exponent is
half the even block size; deleting two ports lowers it by one. -/
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable

/-- The ratio coset (-1)^k μ_N for a block with 2k ports. -/
def PhaseRatio (N k : ℕ) (r : AlgebraicComplex) : Prop :=
  ∃ s : rootsOfUnity N AlgebraicComplex, r = (-1 : AlgebraicComplex) ^ k * (s.val : AlgebraicComplex)

lemma PhaseRatio.ne_zero {N k : ℕ} {r : AlgebraicComplex} (hr : PhaseRatio N k r) : r ≠ 0 := by
  obtain ⟨s, rfl⟩ := hr
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Units.ne_zero s.val)

lemma PhaseRatio.mul_root {N k : ℕ} {r : AlgebraicComplex} (hr : PhaseRatio N k r)
    (s : rootsOfUnity N AlgebraicComplex) : PhaseRatio N k ((s.val : AlgebraicComplex) * r) := by
  obtain ⟨t, rfl⟩ := hr
  exact ⟨s * t, by simp only [Subgroup.coe_mul, Units.val_mul]; ring⟩

lemma PhaseRatio.inv {N k : ℕ} {r : AlgebraicComplex} (hr : PhaseRatio N k r) :
    PhaseRatio N k r⁻¹ := by
  obtain ⟨s, rfl⟩ := hr
  refine ⟨s⁻¹, ?_⟩
  simp [mul_inv_rev, ← inv_pow, mul_comm]

/-- Same-block contraction in either supported orientation. -/
lemma PhaseRatio.delete_pair {N k : ℕ} {r : AlgebraicComplex}
    (hr : PhaseRatio N (k + 1) r) (s : rootsOfUnity N AlgebraicComplex) :
    PhaseRatio N k (-(s.val : AlgebraicComplex) * r) := by
  obtain ⟨t, rfl⟩ := hr
  refine ⟨s * t, ?_⟩
  simp only [Subgroup.coe_mul, Units.val_mul, pow_succ]
  ring

lemma PhaseRatio.delete_pair_inverse {N k : ℕ} {r : AlgebraicComplex}
    (hr : PhaseRatio N (k + 1) r) (s : rootsOfUnity N AlgebraicComplex) :
    PhaseRatio N k (-r / (s.val : AlgebraicComplex)) := by
  have h := hr.delete_pair s⁻¹
  convert h using 1 <;> simp [div_eq_mul_inv, mul_comm]

/-- Distinct blocks of sizes 2(k+1), 2(l+1) merge after deleting one port
from each; their new half-size is k+l+1. -/
lemma PhaseRatio.merge_blocks {N k l : ℕ} {r t : AlgebraicComplex}
    (hr : PhaseRatio N (k + 1) r) (ht : PhaseRatio N (l + 1) t)
    (s : rootsOfUnity N AlgebraicComplex) :
    PhaseRatio N (k + l + 1) (-(s.val : AlgebraicComplex) * r * t) := by
  obtain ⟨u, rfl⟩ := hr
  obtain ⟨v, rfl⟩ := ht
  refine ⟨s * u * v, ?_⟩
  simp only [Subgroup.coe_mul, Units.val_mul, pow_add, pow_one]
  ring

lemma PhaseRatio.merge_blocks_inverse {N k l : ℕ} {r t : AlgebraicComplex}
    (hr : PhaseRatio N (k + 1) r) (ht : PhaseRatio N (l + 1) t)
    (s : rootsOfUnity N AlgebraicComplex) :
    PhaseRatio N (k + l + 1) (-(s.val : AlgebraicComplex) * r * t⁻¹) :=
  hr.merge_blocks ht.inv s

/-- Transposing the minus kernel adds only a nonzero scalar and inverts its
root phase, as used by the source's orientation closure. -/
lemma minusKernel_transpose (s : AlgebraicComplex) (hs : s ≠ 0) :
    (minusKernel s).transpose = (-s) • minusKernel s⁻¹ := by
  funext i j
  cases i <;> cases j <;> simp [minusKernel, Matrix.transpose_apply, hs]

end
end Paper2.HeightOne.PhaseCards
