import ComplexCSP.Algebra.EffectiveRootsTrace

/-!
# Computable polynomial bounds and trace Gram matrices

An integer monic annihilating polynomial gives a natural Cauchy bound. When its
rational image is the generator's minimal polynomial, its companion matrix
computes every trace Gram entry by rational matrix powers and matrix trace.
-/

namespace ComplexCSP.EffectiveRoots

open scoped BigOperators Matrix

/-- A deliberately coarse but executable natural bound for every complex root
of a monic integer polynomial. -/
def integerCauchyBound (p : Polynomial ℤ) : ℕ :=
  (∑ i ∈ Finset.range p.natDegree, (p.coeff i).natAbs) + 1

theorem integerCauchyBound_pos (p : Polynomial ℤ) : 0 < integerCauchyBound p :=
  Nat.succ_pos _

/-- Cauchy's analytic bound is bounded by the explicit integer coefficient sum. -/
theorem integerPolynomial_cauchyBound_le (p : Polynomial ℤ) (hp : p.Monic) :
    (p.map (Int.castRingHom ℂ)).cauchyBound ≤ (integerCauchyBound p : NNReal) := by
  have hdegree : (p.map (Int.castRingHom ℂ)).natDegree = p.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (Int.cast_injective) p
  have hlead : (p.map (Int.castRingHom ℂ)).leadingCoeff = 1 :=
    (hp.map _).leadingCoeff
  have hsup : (Finset.range p.natDegree).sup
      (fun i ↦ ‖(p.map (Int.castRingHom ℂ)).coeff i‖₊) ≤
        ((∑ i ∈ Finset.range p.natDegree, (p.coeff i).natAbs : ℕ) : NNReal) := by
    apply Finset.sup_le
    intro i hi
    change ‖(p.map (Int.castRingHom ℂ)).coeff i‖ ≤
      ((∑ j ∈ Finset.range p.natDegree, (p.coeff j).natAbs : ℕ) : ℝ)
    have hnat : (p.coeff i).natAbs ≤ ∑ j ∈ Finset.range p.natDegree, (p.coeff j).natAbs :=
      Finset.single_le_sum (f := fun j ↦ (p.coeff j).natAbs) (fun j _ ↦ Nat.zero_le _) hi
    have hreal : ((p.coeff i).natAbs : ℝ) ≤
        ((∑ j ∈ Finset.range p.natDegree, (p.coeff j).natAbs : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom, Complex.norm_intCast,
      Nat.cast_natAbs, Int.cast_abs] using hreal
  rw [Polynomial.cauchyBound, hdegree, hlead]
  simpa only [nnnorm_one, div_one, integerCauchyBound, Nat.cast_add, Nat.cast_one, add_comm] using
    add_le_add_right hsup 1

theorem norm_root_le_integerCauchyBound (p : Polynomial ℤ) (hp : p.Monic)
    (z : ℂ) (hz : Polynomial.aeval z p = 0) : ‖z‖ ≤ integerCauchyBound p := by
  have hroot : (p.map (Int.castRingHom ℂ)).IsRoot z := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map]
    exact hz
  have h := hroot.norm_lt_cauchyBound (hp.map (Int.castRingHom ℂ)).ne_zero
  have hle := h.le.trans (integerPolynomial_cauchyBound_le p hp)
  exact_mod_cast hle

/-- The rational companion matrix read directly from integer polynomial data. -/
def companionMatrix (n : ℕ) (p : Polynomial ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ if j.val + 1 = n then -(p.coeff i.val : ℚ)
    else if i.val = j.val + 1 then 1 else 0

/-- Every trace Gram entry is computed from a rational matrix power. -/
def gramFromPolynomial (n : ℕ) (p : Polynomial ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ (companionMatrix n p ^ (i.val + j.val)).trace

variable {K : Type*} [Field K] [NumberField K]

/-- A monic integer annihilator bounds every conjugate of the generator. -/
theorem embedding_gen_le_integerCauchyBound (pb : PowerBasis ℚ K)
    (p : Polynomial ℤ) (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (σ : K →ₐ[ℚ] ℂ) : ‖σ pb.gen‖ ≤ integerCauchyBound p := by
  apply norm_root_le_integerCauchyBound p hp
  calc
    _ = (σ.restrictScalars ℤ) (Polynomial.aeval pb.gen p) :=
      Polynomial.aeval_algHom_apply (σ.restrictScalars ℤ) pb.gen p
    _ = 0 := by rw [hroot, map_zero]

/-- The runtime companion matrix is the generator's actual multiplication
matrix in its certified power basis. -/
theorem companionMatrix_eq_leftMulMatrix (pb : PowerBasis ℚ K) (p : Polynomial ℤ)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen) :
    companionMatrix pb.dim p = Algebra.leftMulMatrix pb.basis pb.gen := by
  rw [pb.leftMulMatrix]
  ext i j
  simp only [companionMatrix, Matrix.of_apply, pb.minpolyGen_eq, ← hpoly,
    Polynomial.coeff_map, Int.coe_castRingHom]

/-- Thus the computed rational Gram matrix is exactly the mathematical trace
Gram matrix, whose invertibility has already been proved. -/
theorem gramFromPolynomial_eq_traceGram (pb : PowerBasis ℚ K) (p : Polynomial ℤ)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen) :
    gramFromPolynomial pb.dim p = traceGram pb := by
  ext i j
  change (companionMatrix pb.dim p ^ (i.val + j.val)).trace =
    Algebra.trace ℚ K (pb.gen ^ (i.val + j.val))
  rw [Algebra.trace_eq_matrix_trace pb.basis, map_pow,
    companionMatrix_eq_leftMulMatrix pb p hpoly]

/-- Root candidates now use only runtime dimension and integer polynomial data;
no supplied embedding bound or supplied rational matrix inverse is needed. -/
theorem root_coordinates_mem_computed_candidates (pb : PowerBasis ℚ K)
    (p : Polynomial ℤ) (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen)
    (ζ : K) (hζ : IsOfFinOrder ζ) :
    pb.basis.equivFun ζ ∈ candidateCoordinates (gramFromPolynomial pb.dim p) (integerCauchyBound p) := by
  rw [gramFromPolynomial_eq_traceGram pb p hpoly]
  exact root_coordinates_mem_candidates pb ⟨p, hp, hroot⟩ (integerCauchyBound p)
    (embedding_gen_le_integerCauchyBound pb p hp hroot) ζ hζ

/-- The order bound for the fully polynomial-derived rational candidate set. -/
theorem root_order_le_computed_candidate_card (pb : PowerBasis ℚ K)
    (p : Polynomial ℤ) (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen)
    (ζ : K) (hζ : IsOfFinOrder ζ) :
    orderOf ζ ≤ (candidateCoordinates (gramFromPolynomial pb.dim p) (integerCauchyBound p)).card := by
  rw [gramFromPolynomial_eq_traceGram pb p hpoly]
  exact root_order_le_candidate_card pb ⟨p, hp, hroot⟩ (integerCauchyBound p)
    (embedding_gen_le_integerCauchyBound pb p hp hroot) ζ hζ

/-- The factorial exponent is computed from the explicit polynomial-derived
finite candidate set and provably kills every root of unity in the field. -/
theorem root_pow_computed_exponent (pb : PowerBasis ℚ K)
    (p : Polynomial ℤ) (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen)
    (ζ : K) (hζ : IsOfFinOrder ζ) :
    ζ ^ candidateExponent (gramFromPolynomial pb.dim p) (integerCauchyBound p) = 1 := by
  rw [gramFromPolynomial_eq_traceGram pb p hpoly]
  exact root_pow_candidateExponent pb ⟨p, hp, hroot⟩ (integerCauchyBound p)
    (embedding_gen_le_integerCauchyBound pb p hp hroot) ζ hζ

end ComplexCSP.EffectiveRoots
