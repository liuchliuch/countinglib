import Paper2.ExactInput.AnnihilatorHeight
import Paper2.ExactInput.NonzeroRootBound
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! Root separation for variable rational polynomials of bounded degree.
The difference annihilator uses a fixed-size companion matrix; its entries are
runtime rational coefficients, so no fixed-number-field presentation is used.
-/
namespace Paper2.ExactInput.FixedRootCodec.VariableSeparation
open Paper2.Algebraic Polynomial
open scoped BigOperators Matrix

noncomputable section

private theorem rational_algebraMap (q : ℚ) :
    (algebraMap ℚ ℂ) q = (q : ℂ) := by
  simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℂ) q

/-- The row-oriented companion matrix for a monic polynomial. -/
def companion {n : ℕ} (v : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ := fun i j =>
  if i.val + 1 < n then if j.val = i.val + 1 then 1 else 0 else -v j

/-- Multiplication by the difference of the two formal roots. -/
def differenceMatrix {n : ℕ} (v : Fin n → ℚ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℚ := fun ij kl =>
  (if ij.2 = kl.2 then companion v ij.1 kl.1 else 0) -
    (if ij.1 = kl.1 then companion v ij.2 kl.2 else 0)

def differencePolynomial {n : ℕ} (v : Fin n → ℚ) : ℚ[X] :=
  (differenceMatrix v).charpoly

theorem differencePolynomial_monic {n : ℕ} (v : Fin n → ℚ) :
    (differencePolynomial v).Monic := Matrix.charpoly_monic _

private theorem rationalBitHeight_neg (q : ℚ) :
    rationalBitHeight (-q) = rationalBitHeight q := by
  simp [rationalBitHeight, rationalHeight]

private theorem companion_height {n B : ℕ} (v : Fin n → ℚ)
    (hv : ∀ i, rationalBitHeight (v i) ≤ B) (i j : Fin n) :
    rationalBitHeight (companion v i j) ≤ B + 1 := by
  unfold companion
  split_ifs
  · change 1 ≤ B + 1; omega
  · change 1 ≤ B + 1; omega
  · rw [rationalBitHeight_neg]
    exact (hv j).trans (by omega)

private theorem differenceMatrix_height {n B : ℕ} (v : Fin n → ℚ)
    (hv : ∀ i, rationalBitHeight (v i) ≤ B) (ij kl : Fin n × Fin n) :
    rationalBitHeight (differenceMatrix v ij kl) ≤ 2 * B + 4 := by
  have hl : rationalBitHeight
      (if ij.2 = kl.2 then companion v ij.1 kl.1 else 0) ≤ B + 1 := by
    split_ifs
    · exact companion_height v hv _ _
    · change 1 ≤ B + 1; omega
  have hr : rationalBitHeight
      (if ij.1 = kl.1 then companion v ij.2 kl.2 else 0) ≤ B + 1 := by
    split_ifs
    · exact companion_height v hv _ _
    · change 1 ≤ B + 1; omega
  unfold differenceMatrix
  rw [sub_eq_add_neg]
  have hh := rationalBitHeight_add
    (if ij.2 = kl.2 then companion v ij.1 kl.1 else 0)
    (-(if ij.1 = kl.1 then companion v ij.2 kl.2 else 0))
  rw [rationalBitHeight_neg] at hh
  omega

/-- The universal characteristic polynomial supplies a uniform coefficient
height bound for every matrix of the fixed dimension. -/
theorem differencePolynomial_height (n : ℕ) :
    ∃ C : ℕ, ∀ B (v : Fin n → ℚ), (∀ i, rationalBitHeight (v i) ≤ B) →
      ∀ j, rationalBitHeight ((differencePolynomial v).coeff j) ≤ C * (B + 1) := by
  obtain ⟨D, hD⟩ := mvPolynomial_family_height_bound
    (fun j : Fin (n * n + 1) =>
      (Matrix.charpoly.univ ℚ (Fin n × Fin n)).coeff j.val)
  refine ⟨5 * D + 1, fun B v hv j => ?_⟩
  by_cases hj : j < n * n + 1
  · have hd := hD (2 * B + 4)
      (fun ij : (Fin n × Fin n) × (Fin n × Fin n) => differenceMatrix v ij.1 ij.2)
      (fun ij => differenceMatrix_height v hv ij.1 ij.2) ⟨j, hj⟩
    have he := Matrix.charpoly.univ_coeff_eval₂Hom (Fin n × Fin n) (RingHom.id ℚ)
      (fun ij : (Fin n × Fin n) × (Fin n × Fin n) => differenceMatrix v ij.1 ij.2) j
    change MvPolynomial.eval _ _ = (differencePolynomial v).coeff j at he
    rw [he] at hd
    nlinarith
  · have hd : (differencePolynomial v).natDegree < j := by
      simp only [differencePolynomial, Matrix.charpoly_natDegree_eq_dim,
        Fintype.card_prod, Fintype.card_fin]
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd]
    change 1 ≤ (5 * D + 1) * (B + 1)
    have := Nat.mul_pos (by omega : 0 < 5 * D + 1) (by omega : 0 < B + 1)
    omega

private theorem companion_eigenvector {n : ℕ} (v : Fin n → ℚ) (z : ℂ)
    (hz : (∑ j : Fin n, (v j : ℂ) * z ^ j.val) + z ^ n = 0) :
    (companion v).map (algebraMap ℚ ℂ) *ᵥ (fun j => z ^ j.val) =
      z • (fun j : Fin n => z ^ j.val) := by
  ext i
  by_cases hi : i.val + 1 < n
  · rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (⟨i.val + 1, hi⟩ : Fin n)]
    · simp [companion, hi, pow_succ, mul_comm]
    · intro j _ hj
      have hj' : j.val ≠ i.val + 1 := fun he => hj (Fin.ext he)
      simp [companion, hi, hj']
    · simp
  · have he : i.val + 1 = n := by omega
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, companion, hi,
      ↓reduceIte, map_neg, neg_mul, Finset.sum_neg_distrib, Pi.smul_apply,
      smul_eq_mul]
    rw [mul_comm z, ← pow_succ, he]
    simp only [rational_algebraMap]
    linear_combination -hz

private theorem difference_eigenvector {n : ℕ} (v : Fin n → ℚ) (z w : ℂ)
    (hz : (∑ j : Fin n, (v j : ℂ) * z ^ j.val) + z ^ n = 0)
    (hw : (∑ j : Fin n, (v j : ℂ) * w ^ j.val) + w ^ n = 0) :
    (differenceMatrix v).map (algebraMap ℚ ℂ) *ᵥ
      (fun ij => z ^ ij.1.val * w ^ ij.2.val) =
      (z - w) • (fun ij : Fin n × Fin n => z ^ ij.1.val * w ^ ij.2.val) := by
  have ez := companion_eigenvector v z hz
  have ew := companion_eigenvector v w hw
  ext ij
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, differenceMatrix,
    map_sub, sub_mul, Finset.sum_sub_distrib, Fintype.sum_prod_type]
  have hl : (∑ k : Fin n, ∑ l : Fin n,
      (algebraMap ℚ ℂ) (if ij.2 = l then companion v ij.1 k else 0) *
        (z ^ k.val * w ^ l.val)) = z * z ^ ij.1.val * w ^ ij.2.val := by
    simp only [apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, ← mul_assoc, ← Finset.sum_mul]
    have h := congrFun ez ij.1
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
      smul_eq_mul] using congrArg (fun a => a * w ^ ij.2.val) h
  have hr : (∑ k : Fin n, ∑ l : Fin n,
      (algebraMap ℚ ℂ) (if ij.1 = k then companion v ij.2 l else 0) *
        (z ^ k.val * w ^ l.val)) = w * w ^ ij.2.val * z ^ ij.1.val := by
    rw [Finset.sum_comm]
    simp only [apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    have h := congrFun ew ij.2
    calc
      _ = (∑ l : Fin n, (algebraMap ℚ ℂ) (companion v ij.2 l) * w ^ l.val) *
          z ^ ij.1.val := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro l _
            ring
      _ = _ := by
        simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
          smul_eq_mul] using congrArg (fun a => a * z ^ ij.1.val) h
  rw [hl, hr]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Every difference of roots obeying the monic coefficient equation is a
root of the genuine rational characteristic polynomial. -/
theorem differencePolynomial_root {n : ℕ} (hn : 0 < n) (v : Fin n → ℚ) (z w : ℂ)
    (hz : (∑ j : Fin n, (v j : ℂ) * z ^ j.val) + z ^ n = 0)
    (hw : (∑ j : Fin n, (v j : ℂ) * w ^ j.val) + w ^ n = 0) :
    Polynomial.aeval (z - w) (differencePolynomial v) = 0 := by
  let A := (differenceMatrix v).map (algebraMap ℚ ℂ)
  let u : Fin n × Fin n → ℂ := fun ij => z ^ ij.1.val * w ^ ij.2.val
  have hu : u ≠ 0 := by
    intro h
    have he := congrFun h (⟨0, hn⟩, ⟨0, hn⟩)
    simp [u] at he
  have he : A *ᵥ u = (z - w) • u := difference_eigenvector v z w hz hw
  have hz0 : (Matrix.scalar (Fin n × Fin n) (z - w) - A) *ᵥ u = 0 := by
    rw [Matrix.sub_mulVec, he]
    ext ij
    simp [Matrix.scalar, Matrix.mulVec_diagonal]
  have hd := (Matrix.exists_mulVec_eq_zero_iff).mp ⟨u, hu, hz0⟩
  rw [← Matrix.eval_charpoly] at hd
  simpa only [A, differencePolynomial, Matrix.charpoly_map, Polynomial.eval_map,
    Polynomial.aeval_def] using hd

private theorem monic_root_equation {n : ℕ} {p : ℚ[X]} (hp : p.Monic)
    (hd : p.natDegree = n) {z : ℂ} (hz : Polynomial.aeval z p = 0) :
    (∑ j : Fin n, (p.coeff j.val : ℂ) * z ^ j.val) + z ^ n = 0 := by
  rw [Polynomial.aeval_eq_sum_range, hd, Finset.sum_range_succ] at hz
  have hc : p.coeff n = 1 := hd ▸ hp.coeff_natDegree
  rw [hc, one_smul] at hz
  rw [Finset.sum_range] at hz
  simpa only [Algebra.smul_def, rational_algebraMap] using hz

/-- A uniform affine exponent separates roots of every monic polynomial of
the given positive degree, even if that polynomial has repeated roots. -/
theorem monic_root_separation (n : ℕ) (hn : 0 < n) :
    ∃ C : ℕ, ∀ B (p : ℚ[X]), p.Monic → p.natDegree = n →
      (∀ j, rationalBitHeight (p.coeff j) ≤ B) →
      ∀ z w : ℂ, Polynomial.aeval z p = 0 → Polynomial.aeval w p = 0 → z ≠ w →
        1 ≤ ‖z - w‖ * (2 : ℝ) ^ (C * (B + 1)) := by
  obtain ⟨C, hC⟩ := differencePolynomial_height n
  refine ⟨2 * C + 1, fun B p hp hd hh z w hz hw hne => ?_⟩
  let v : Fin n → ℚ := fun i => p.coeff i.val
  have hr := differencePolynomial_root hn v z w
    (monic_root_equation hp hd hz) (monic_root_equation hp hd hw)
  have hb := nonzero_root_norm_lower (differencePolynomial_monic v).ne_zero
    (hC B v (fun i => hh i.val)) (sub_ne_zero.mpr hne) hr
  have he : 2 * (C * (B + 1)) + 1 ≤ (2 * C + 1) * (B + 1) := by nlinarith
  exact hb.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he) (norm_nonneg _))

/-- Leading-coefficient normalization and zero padding preserve every root
while giving a monic polynomial of one fixed positive degree. -/
def paddedPolynomial (d : ℕ) (p : ℚ[X]) : ℚ[X] :=
  (p * C p.leadingCoeff⁻¹) * X ^ (d + 1 - p.natDegree)

theorem paddedPolynomial_monic (d : ℕ) {p : ℚ[X]} (hp : p ≠ 0) :
    (paddedPolynomial d p).Monic :=
  (monic_mul_leadingCoeff_inv hp).mul (monic_X_pow _)

theorem paddedPolynomial_degree (d : ℕ) {p : ℚ[X]} (hp : p ≠ 0)
    (hd : p.natDegree ≤ d) : (paddedPolynomial d p).natDegree = d + 1 := by
  rw [paddedPolynomial, (monic_mul_leadingCoeff_inv hp).natDegree_mul (monic_X_pow _),
    natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hp)), natDegree_X_pow]
  omega

theorem paddedPolynomial_height (d B : ℕ) (p : ℚ[X])
    (hp : ∀ j, rationalBitHeight (p.coeff j) ≤ B) (j : ℕ) :
    rationalBitHeight ((paddedPolynomial d p).coeff j) ≤ 2 * B + 1 := by
  rw [paddedPolynomial, coeff_mul_X_pow']
  split_ifs
  · rw [coeff_mul_C]
    have hl : rationalBitHeight p.leadingCoeff⁻¹ ≤ B :=
      (rationalBitHeight_inv_le _).trans (hp p.natDegree)
    have hm := rationalBitHeight_mul (p.coeff (j - (d + 1 - p.natDegree))) p.leadingCoeff⁻¹
    have hc := hp (j - (d + 1 - p.natDegree))
    omega
  · change 1 ≤ 2 * B + 1; omega

theorem paddedPolynomial_root (d : ℕ) (p : ℚ[X]) {z : ℂ}
    (hz : Polynomial.aeval z p = 0) : Polynomial.aeval z (paddedPolynomial d p) = 0 := by
  simp [paddedPolynomial, hz]

/-- Distinct complex roots of an arbitrary nonzero rational polynomial of
bounded degree have separation controlled by its coefficient bit heights. -/
theorem bounded_degree_root_separation (d : ℕ) :
    ∃ C : ℕ, ∀ B (p : ℚ[X]), p ≠ 0 → p.natDegree ≤ d →
      (∀ j, rationalBitHeight (p.coeff j) ≤ B) →
      ∀ z w : ℂ, Polynomial.aeval z p = 0 → Polynomial.aeval w p = 0 → z ≠ w →
        1 ≤ ‖z - w‖ * (2 : ℝ) ^ (C * (B + 1)) := by
  obtain ⟨C, hC⟩ := monic_root_separation (d + 1) (by omega)
  refine ⟨2 * C, fun B p hp hd hh z w hz hw hne => ?_⟩
  have hs := hC (2 * B + 1) (paddedPolynomial d p) (paddedPolynomial_monic d hp)
    (paddedPolynomial_degree d hp hd) (paddedPolynomial_height d B p hh) z w
    (paddedPolynomial_root d p hz) (paddedPolynomial_root d p hw) hne
  convert hs using 1
  congr 2
  ring

end
end Paper2.ExactInput.FixedRootCodec.VariableSeparation
