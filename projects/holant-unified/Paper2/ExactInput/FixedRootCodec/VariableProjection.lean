import Paper2.ExactInput.FixedRootCodec.VariableSeparation
import Mathlib.Algebra.Polynomial.OfFn

/-! Rational projection polynomials for all real and imaginary parts of the
roots of a variable rational polynomial. A companion Kronecker sum handles
the real part; the negative square of its Kronecker difference handles the
imaginary part without adjoining the imaginary unit to the coefficient field.
-/
namespace Paper2.ExactInput.FixedRootCodec.VariableProjection
open Paper2.Algebraic Polynomial
open scoped BigOperators Matrix
noncomputable section

private theorem rational_algebraMap (q : ℚ) :
    (algebraMap ℚ ℂ) q = (q : ℂ) := by
  simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℂ) q

def companionSymbolic (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℚ) :=
  fun i j => if i.val + 1 < n then if j.val = i.val + 1 then 1 else 0
    else -MvPolynomial.X j

def tensorSymbolic (n : ℕ) (s : ℚ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) (MvPolynomial (Fin n) ℚ) := fun ij kl =>
  (if ij.2 = kl.2 then companionSymbolic n ij.1 kl.1 else 0) +
    MvPolynomial.C s * (if ij.1 = kl.1 then companionSymbolic n ij.2 kl.2 else 0)

def tensorMatrix {n : ℕ} (v : Fin n → ℚ) (s : ℚ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℚ := fun ij kl =>
  (if ij.2 = kl.2 then VariableSeparation.companion v ij.1 kl.1 else 0) +
    s * (if ij.1 = kl.1 then VariableSeparation.companion v ij.2 kl.2 else 0)

theorem tensorSymbolic_eval {n : ℕ} (v : Fin n → ℚ) (s : ℚ) :
    (tensorSymbolic n s).map (MvPolynomial.eval v) = tensorMatrix v s := by
  have hc : ∀ i j : Fin n, MvPolynomial.eval v (companionSymbolic n i j) =
      VariableSeparation.companion v i j := by
    intro i j
    unfold companionSymbolic VariableSeparation.companion
    split_ifs <;> simp
  ext ij kl
  by_cases hl : ij.2 = kl.2 <;> by_cases hr : ij.1 = kl.1 <;>
    simp only [tensorSymbolic, tensorMatrix, Matrix.map_apply, hl, hr, ↓reduceIte,
      map_add, map_mul, map_zero, MvPolynomial.eval_C, hc]

def realSymbolic (n : ℕ) : Polynomial (MvPolynomial (Fin n) ℚ) :=
  (tensorSymbolic n 1).charpoly.comp (C (MvPolynomial.C 2) * X)

def imaginarySymbolic (n : ℕ) : Polynomial (MvPolynomial (Fin n) ℚ) :=
  (-(tensorSymbolic n (-1) * tensorSymbolic n (-1))).charpoly.comp
    (C (MvPolynomial.C 4) * X ^ 2)

def realProjection {n : ℕ} (v : Fin n → ℚ) : ℚ[X] :=
  (realSymbolic n).map (MvPolynomial.eval v)

def imaginaryProjection {n : ℕ} (v : Fin n → ℚ) : ℚ[X] :=
  (imaginarySymbolic n).map (MvPolynomial.eval v)

theorem realProjection_eq {n : ℕ} (v : Fin n → ℚ) :
    realProjection v = (tensorMatrix v 1).charpoly.comp (C 2 * X) := by
  rw [realProjection, realSymbolic, Polynomial.map_comp, ← Matrix.charpoly_map,
    tensorSymbolic_eval]
  simp

theorem imaginaryProjection_eq {n : ℕ} (v : Fin n → ℚ) :
    imaginaryProjection v = (-(tensorMatrix v (-1) * tensorMatrix v (-1))).charpoly.comp
      (C 4 * X ^ 2) := by
  rw [imaginaryProjection, imaginarySymbolic, Polynomial.map_comp, ← Matrix.charpoly_map]
  have hm : (-(tensorSymbolic n (-1) * tensorSymbolic n (-1))).map
      (MvPolynomial.eval v) = -(tensorMatrix v (-1) * tensorMatrix v (-1)) := by
    simp only [Matrix.map_neg _ (map_neg (MvPolynomial.eval v)), Matrix.map_mul,
      tensorSymbolic_eval]
  rw [hm]
  simp

theorem realProjection_ne_zero {n : ℕ} (v : Fin n → ℚ) : realProjection v ≠ 0 := by
  rw [realProjection_eq]
  intro h
  rcases comp_eq_zero_iff.mp h with h | ⟨_, h⟩
  · exact (Matrix.charpoly_monic _).ne_zero h
  · have hc := congrArg (fun p : ℚ[X] => p.coeff 1) h
    norm_num [coeff_C_mul] at hc

theorem imaginaryProjection_ne_zero {n : ℕ} (v : Fin n → ℚ) :
    imaginaryProjection v ≠ 0 := by
  rw [imaginaryProjection_eq]
  intro h
  rcases comp_eq_zero_iff.mp h with h | ⟨_, h⟩
  · exact (Matrix.charpoly_monic _).ne_zero h
  · have hc := congrArg (fun p : ℚ[X] => p.coeff 2) h
    norm_num [coeff_C_mul] at hc

theorem realProjection_degree {n : ℕ} (v : Fin n → ℚ) :
    (realProjection v).natDegree = n * n := by
  rw [realProjection_eq, natDegree_comp]
  simp [natDegree_C_mul (by norm_num : (2 : ℚ) ≠ 0), Matrix.charpoly_natDegree_eq_dim]

theorem imaginaryProjection_degree {n : ℕ} (v : Fin n → ℚ) :
    (imaginaryProjection v).natDegree = 2 * (n * n) := by
  rw [imaginaryProjection_eq, natDegree_comp]
  simp [natDegree_C_mul (by norm_num : (4 : ℚ) ≠ 0), Matrix.charpoly_natDegree_eq_dim,
    Nat.mul_comm]

private theorem companion_eigenvector {n : ℕ} (v : Fin n → ℚ) (z : ℂ)
    (hz : (∑ j : Fin n, (v j : ℂ) * z ^ j.val) + z ^ n = 0) :
    (VariableSeparation.companion v).map (algebraMap ℚ ℂ) *ᵥ (fun j => z ^ j.val) =
      z • (fun j : Fin n => z ^ j.val) := by
  ext i
  by_cases hi : i.val + 1 < n
  · rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (⟨i.val + 1, hi⟩ : Fin n)]
    · simp [VariableSeparation.companion, hi, pow_succ, mul_comm]
    · intro j _ hj
      have hj' : j.val ≠ i.val + 1 := fun he => hj (Fin.ext he)
      simp [VariableSeparation.companion, hi, hj']
    · simp
  · have he : i.val + 1 = n := by omega
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, VariableSeparation.companion,
      hi, ↓reduceIte, map_neg, neg_mul, Finset.sum_neg_distrib, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm z, ← pow_succ, he]
    simp only [rational_algebraMap]
    linear_combination -hz

private theorem tensor_eigenvector {n : ℕ} (v : Fin n → ℚ) (s : ℚ) (z w : ℂ)
    (hz : (∑ j : Fin n, (v j : ℂ) * z ^ j.val) + z ^ n = 0)
    (hw : (∑ j : Fin n, (v j : ℂ) * w ^ j.val) + w ^ n = 0) :
    (tensorMatrix v s).map (algebraMap ℚ ℂ) *ᵥ
      (fun ij => z ^ ij.1.val * w ^ ij.2.val) =
      (z + (s : ℂ) * w) • (fun ij : Fin n × Fin n => z ^ ij.1.val * w ^ ij.2.val) := by
  have ez := companion_eigenvector v z hz
  have ew := companion_eigenvector v w hw
  ext ij
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, tensorMatrix,
    map_add, map_mul, add_mul, Finset.sum_add_distrib, Fintype.sum_prod_type]
  have hl : (∑ k : Fin n, ∑ l : Fin n,
      (algebraMap ℚ ℂ) (if ij.2 = l then VariableSeparation.companion v ij.1 k else 0) *
        (z ^ k.val * w ^ l.val)) = z * z ^ ij.1.val * w ^ ij.2.val := by
    simp only [apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, ← mul_assoc, ← Finset.sum_mul]
    have h := congrFun ez ij.1
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
      smul_eq_mul] using congrArg (fun a => a * w ^ ij.2.val) h
  have hr : (∑ k : Fin n, ∑ l : Fin n,
      (algebraMap ℚ ℂ) s *
        (algebraMap ℚ ℂ) (if ij.1 = k then VariableSeparation.companion v ij.2 l else 0) *
        (z ^ k.val * w ^ l.val)) = (s : ℂ) * w * w ^ ij.2.val * z ^ ij.1.val := by
    rw [Finset.sum_comm]
    simp only [apply_ite, map_zero, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, rational_algebraMap]
    have h := congrFun ew ij.2
    calc
      _ = (s : ℂ) * ((∑ l : Fin n,
          (algebraMap ℚ ℂ) (VariableSeparation.companion v ij.2 l) * w ^ l.val) *
            z ^ ij.1.val) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        simp only [rational_algebraMap]
        ring
      _ = _ := by
        have he := congrArg (fun a => (s : ℂ) * (a * z ^ ij.1.val)) h
        simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
          smul_eq_mul, mul_assoc] using he
  rw [hl, hr]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem eigenvalue_root {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (u : ι → ℂ) (hu : u ≠ 0) (z : ℂ)
    (hz : A.map (algebraMap ℚ ℂ) *ᵥ u = z • u) :
    Polynomial.aeval z A.charpoly = 0 := by
  have hz0 : (Matrix.scalar ι z - A.map (algebraMap ℚ ℂ)) *ᵥ u = 0 := by
    rw [Matrix.sub_mulVec, hz]
    ext i
    simp [Matrix.scalar, Matrix.mulVec_diagonal]
  have hd := (Matrix.exists_mulVec_eq_zero_iff).mp ⟨u, hu, hz0⟩
  rw [← Matrix.eval_charpoly] at hd
  simpa only [Matrix.charpoly_map, Polynomial.eval_map, Polynomial.aeval_def] using hd

private theorem monic_root_equation {n : ℕ} {p : ℚ[X]} (hp : p.Monic)
    (hd : p.natDegree = n) {z : ℂ} (hz : Polynomial.aeval z p = 0) :
    (∑ j : Fin n, (p.coeff j.val : ℂ) * z ^ j.val) + z ^ n = 0 := by
  rw [Polynomial.aeval_eq_sum_range, hd, Finset.sum_range_succ] at hz
  have hc : p.coeff n = 1 := hd ▸ hp.coeff_natDegree
  rw [hc, one_smul, Finset.sum_range] at hz
  simpa only [Algebra.smul_def, rational_algebraMap] using hz

/-- Both projection polynomials cover every complex root of the monic source. -/
theorem projections_cover_monic {n : ℕ} (hn : 0 < n) (p : ℚ[X]) (hp : p.Monic)
    (hd : p.natDegree = n) {z : ℂ} (hz : Polynomial.aeval z p = 0) :
    Polynomial.aeval (z.re : ℂ) (realProjection (fun i : Fin n => p.coeff i.val)) = 0 ∧
    Polynomial.aeval (z.im : ℂ) (imaginaryProjection (fun i : Fin n => p.coeff i.val)) = 0 := by
  let v : Fin n → ℚ := fun i => p.coeff i.val
  have hq := monic_root_equation hp hd hz
  have hc : (∑ j : Fin n, (v j : ℂ) * (star z) ^ j.val) + (star z) ^ n = 0 := by
    simpa only [v, map_add, map_sum, map_mul, map_pow, map_ratCast, map_zero,
      starRingEnd_apply] using
      congrArg (starRingEnd ℂ) hq
  let u : Fin n × Fin n → ℂ := fun ij => z ^ ij.1.val * (star z) ^ ij.2.val
  have hu : u ≠ 0 := by
    intro h
    have he := congrFun h (⟨0, hn⟩, ⟨0, hn⟩)
    simp [u] at he
  have hs : z + star z = 2 * (z.re : ℂ) := by
    apply Complex.ext <;> simp
    ring
  have hi : -((z - star z) * (z - star z)) = 4 * (z.im : ℂ) ^ 2 := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, pow_two]
    ring
  constructor
  · have he := tensor_eigenvector v 1 z (star z) hq hc
    simp only [Rat.cast_one, one_mul, hs] at he
    have hr := eigenvalue_root (tensorMatrix v 1) u hu (2 * (z.re : ℂ)) he
    rw [realProjection_eq, Polynomial.aeval_comp]
    simpa using hr
  · let D := tensorMatrix v (-1)
    have he := tensor_eigenvector v (-1) z (star z) hq hc
    simp only [Rat.cast_neg, Rat.cast_one, neg_one_mul, ← sub_eq_add_neg] at he
    have hsq : (-(D * D)).map (algebraMap ℚ ℂ) *ᵥ u =
        (4 * (z.im : ℂ) ^ 2) • u := by
      rw [Matrix.map_neg _ (map_neg (algebraMap ℚ ℂ)), Matrix.map_mul,
        Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
        he, Matrix.mulVec_smul, he, smul_smul]
      rw [← neg_smul, hi]
    have hr := eigenvalue_root (-(D * D)) u hu (4 * (z.im : ℂ) ^ 2) hsq
    rw [imaginaryProjection_eq, Polynomial.aeval_comp]
    simpa [D] using hr

def paddedCoefficients (d : ℕ) (p : ℚ[X]) : Fin (d + 1) → ℚ :=
  fun i => (VariableSeparation.paddedPolynomial d p).coeff i.val

def realPolynomial (d : ℕ) (p : ℚ[X]) : ℚ[X] := realProjection (paddedCoefficients d p)
def imaginaryPolynomial (d : ℕ) (p : ℚ[X]) : ℚ[X] := imaginaryProjection (paddedCoefficients d p)

theorem projection_polynomials_ne_zero (d : ℕ) (p : ℚ[X]) :
    realPolynomial d p ≠ 0 ∧ imaginaryPolynomial d p ≠ 0 :=
  ⟨realProjection_ne_zero _, imaginaryProjection_ne_zero _⟩

theorem projection_polynomials_degree (d : ℕ) (p : ℚ[X]) :
    (realPolynomial d p).natDegree = (d + 1) * (d + 1) ∧
      (imaginaryPolynomial d p).natDegree = 2 * ((d + 1) * (d + 1)) :=
  ⟨realProjection_degree _, imaginaryProjection_degree _⟩

theorem projection_polynomials_cover (d : ℕ) (p : ℚ[X]) (hp : p ≠ 0)
    (hd : p.natDegree ≤ d) {z : ℂ} (hz : Polynomial.aeval z p = 0) :
    Polynomial.aeval (z.re : ℂ) (realPolynomial d p) = 0 ∧
      Polynomial.aeval (z.im : ℂ) (imaginaryPolynomial d p) = 0 :=
  projections_cover_monic (by omega) (VariableSeparation.paddedPolynomial d p)
    (VariableSeparation.paddedPolynomial_monic d hp)
    (VariableSeparation.paddedPolynomial_degree d hp hd)
    (VariableSeparation.paddedPolynomial_root d p hz)

end
end Paper2.ExactInput.FixedRootCodec.VariableProjection
