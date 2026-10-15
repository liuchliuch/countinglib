import Paper2.Algebraic.FixedField
import Paper2.ExactInput.ClearedPolynomialHeight
import Paper2.ExactInput.FixedRootCodec.ReverseDenominator
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.FractionRing

/-! Exact coordinate lattice for the reverse fixed-field codec. This module
proves a fixed denominator for every integral field element in the actual
chosen rational basis. It does not assert a runtime root-isolation programme
or a complete RootCode decoder. The trace-dual constants are fixed before any
input, and the varying scalar can be the computable denominator clearing the
input polynomial. -/
namespace Paper2.ExactInput.FixedRootCodec
open Paper2.Algebraic Polynomial
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] {n : ℕ}
local instance : Algebra.IsAlgebraic ℤ ℚ :=
  IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)

theorem exists_natural_integral_multiple (x : K) :
    ∃ c : ℕ, 0 < c ∧ IsIntegral ℤ ((c : K) * x) := by
  obtain ⟨z,hz,hi⟩ :=
    ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).restrictScalars ℤ).exists_integral_multiple
  cases z with
  | ofNat c =>
    refine ⟨c,?_,?_⟩
    · exact Nat.pos_of_ne_zero (fun h => hz (by simp [h]))
    · rw [Algebra.smul_def] at hi
      change IsIntegral ℤ ((algebraMap ℤ K) (c : ℤ) * x) at hi
      simpa only [map_natCast] using hi
  | negSucc c =>
    refine ⟨c+1,Nat.succ_pos c,?_⟩
    rw [Algebra.smul_def,
      show Int.negSucc c = -((c+1 : ℕ) : ℤ) from rfl,map_neg,map_natCast] at hi
    simpa only [neg_mul,neg_neg] using hi.neg

def dualClearing (F : FixedField K n) (i : Fin n) : ℕ :=
  Classical.choose (exists_natural_integral_multiple (F.basis.traceDual i))

theorem dualClearing_positive (F : FixedField K n) (i : Fin n) : 0 < dualClearing F i :=
  (Classical.choose_spec (exists_natural_integral_multiple (F.basis.traceDual i))).1

theorem dualClearing_integral (F : FixedField K n) (i : Fin n) :
    IsIntegral ℤ ((dualClearing F i : K) * F.basis.traceDual i) :=
  (Classical.choose_spec (exists_natural_integral_multiple (F.basis.traceDual i))).2

def coordinateLatticeDenominator (F : FixedField K n) : ℕ := ∏ i : Fin n, dualClearing F i

theorem coordinateLatticeDenominator_pos (F : FixedField K n) :
    0 < coordinateLatticeDenominator F := by
  apply Finset.prod_pos
  intro i _
  exact dualClearing_positive F i

theorem coordinateLatticeDenominator_integral (F : FixedField K n) (i : Fin n) :
    IsIntegral ℤ ((coordinateLatticeDenominator F : K) * F.basis.traceDual i) := by
  have hd : dualClearing F i ∣ coordinateLatticeDenominator F :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  obtain ⟨q,hq⟩ := hd
  have h := (dualClearing_integral F i).smul (q : ℤ)
  simpa only [Algebra.smul_def,hq,Nat.cast_mul,Int.cast_natCast,map_natCast,
    mul_left_comm,mul_assoc] using h

theorem coordinate_trace_dual (F : FixedField K n) (x : K) (i : Fin n) :
    F.basis.repr x i = Algebra.trace ℚ K (x * F.basis.traceDual i) := by
  have h := F.basis.traceDual.traceDual_repr_apply x i
  rw [F.basis.traceDual_traceDual] at h
  exact h

/-- The fixed trace-dual denominator works for every varying integral multiple
of x, so it is suitable for exact nearest-lattice rounding after approximation. -/
theorem coordinates_on_lattice (F : FixedField K n) (D : ℕ) (hD : 0 < D)
    (x : K) (hx : IsIntegral ℤ ((D : K) * x)) :
    ∀ i : Fin n, ∃ a : ℤ,
      F.basis.repr x i = (a : ℚ) / (coordinateLatticeDenominator F * D : ℕ) := by
  intro i
  have hi := (coordinateLatticeDenominator_integral F i).mul hx
  have ht : IsIntegral ℤ (Algebra.trace ℚ K
      (((coordinateLatticeDenominator F : K) * F.basis.traceDual i) * ((D : K) * x))) :=
    Algebra.isIntegral_trace hi
  obtain ⟨a,ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp ht
  have he : ((coordinateLatticeDenominator F : K) * F.basis.traceDual i) * ((D : K) * x) =
      ((coordinateLatticeDenominator F * D : ℕ) : ℚ) • (x * F.basis.traceDual i) := by
    rw [Algebra.smul_def]
    push_cast
    ring
  rw [he,map_smul,← coordinate_trace_dual] at ha
  refine ⟨a,?_⟩
  have hd : ((coordinateLatticeDenominator F * D : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (coordinateLatticeDenominator_pos F) hD).ne'
  apply (eq_div_iff hd).mpr
  simpa only [algebraMap_int_eq,Int.coe_castRingHom,smul_eq_mul,mul_comm] using ha.symm

omit [FiniteDimensional ℚ K] in
/-- Clearing the coefficients of a monic polynomial clears its algebraic
root as an integral element. The multiplier is an explicit natural product. -/
theorem polynomialDenominator_integral_root (d : ℕ) (p : ℚ[X])
    (hp : p.Monic) (hdegree : p.natDegree ≤ d) (x : K) (hx : p.aeval x = 0) :
    IsIntegral ℤ ((polynomialDenominator d p : K) * x) := by
  let P := clearedPolynomial d p
  have hmap := clearedPolynomial_map d p hdegree
  have hroot : P.aeval x = 0 := by
    have h := congrArg (fun q : ℚ[X] => q.aeval x) hmap
    rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl,
      aeval_map_algebraMap,aeval_mul,aeval_C,hx,mul_zero] at h
    exact h
  have hlead : (P.leadingCoeff : ℚ) = polynomialDenominator d p := by
    have h := congrArg Polynomial.leadingCoeff hmap
    rw [Polynomial.leadingCoeff_map_of_injective (Int.castRingHom ℚ).injective_int,
      Polynomial.leadingCoeff_mul,Polynomial.leadingCoeff_C,hp.leadingCoeff,mul_one] at h
    exact h
  have h := isIntegral_leadingCoeff_smul P x hroot
  have he : P.leadingCoeff = (polynomialDenominator d p : ℤ) := by
    exact_mod_cast hlead
  simpa only [Algebra.smul_def,he,map_natCast] using h

theorem polynomial_root_coordinates_on_lattice (F : FixedField K n)
    (d : ℕ) (p : ℚ[X]) (hp : p.Monic) (hdegree : p.natDegree ≤ d)
    (x : K) (hx : p.aeval x = 0) :
    ∀ i : Fin n, ∃ a : ℤ,
      F.basis.repr x i = (a : ℚ) /
        (coordinateLatticeDenominator F * polynomialDenominator d p : ℕ) :=
  coordinates_on_lattice F _ (polynomialDenominator_pos d p) x
    (polynomialDenominator_integral_root d p hp hdegree x hx)

def sparseClearedTerm (D : ℕ) (q : ℚ) : ℤ := q.num * (D / q.den : ℕ)

theorem sparseClearedTerm_correct (D : ℕ) (q : ℚ) (hq : q.den ∣ D) :
    (sparseClearedTerm D q : ℚ) = (D : ℚ) * q := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  have he : ((D / q.den : ℕ) : ℚ) * (q.den : ℚ) = D := by
    exact_mod_cast Nat.div_mul_cancel hq
  have hnum : (q.num : ℚ) = q * (q.den : ℚ) := by
    calc
      _ = ((q.num : ℚ) / q.den) * q.den := (div_mul_cancel₀ _ hd).symm
      _ = _ := by rw [Rat.num_div_den]
  rw [sparseClearedTerm,Int.cast_mul,Int.cast_natCast,hnum]
  calc
    _ = q * (((D / q.den : ℕ) : ℚ) * q.den) := by ring
    _ = _ := by rw [he]; ring

def sparseClearedPolynomial (D : ℕ) : RationalPolynomialCode → ℤ[X]
  | [] => 0
  | (j,q)::p => monomial j (sparseClearedTerm D q) + sparseClearedPolynomial D p

theorem sparseDenominator_member (p : RationalPolynomialCode) (t : ℕ × ℚ) (ht : t ∈ p) :
    t.2.den ∣ sparseDenominator p := by
  induction p with
  | nil => simp at ht
  | cons s p ih =>
    simp only [sparseDenominator,List.map_cons,List.prod_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact dvd_mul_right _ _
    · exact (ih ht).trans (dvd_mul_left _ _)

theorem sparseClearedPolynomial_map (D : ℕ) (p : RationalPolynomialCode)
    (hD : ∀ t ∈ p, t.2.den ∣ D) :
    (sparseClearedPolynomial D p).map (Int.castRingHom ℚ) =
      C (D : ℚ) * p.polynomial := by
  induction p with
  | nil => simp [sparseClearedPolynomial,RationalPolynomialCode.polynomial]
  | cons t p ih =>
    rcases t with ⟨j,q⟩
    rw [sparseClearedPolynomial,Polynomial.map_add,Polynomial.map_monomial,
      ih (fun t ht => hD t (List.mem_cons_of_mem _ ht)),
      RationalPolynomialCode.polynomial,mul_add]
    congr 1
    rw [Polynomial.C_mul_monomial,Int.coe_castRingHom]
    exact congrArg (monomial j)
      (sparseClearedTerm_correct D q (hD (j,q) (List.mem_cons_self)))

omit [FiniteDimensional ℚ K] in
theorem sparseDenominator_integral_root (p : RationalPolynomialCode)
    (hp : p.polynomial.Monic) (x : K) (hx : p.polynomial.aeval x = 0) :
    IsIntegral ℤ ((sparseDenominator p : K) * x) := by
  let P := sparseClearedPolynomial (sparseDenominator p) p
  have hmap := sparseClearedPolynomial_map (sparseDenominator p) p
    (sparseDenominator_member p)
  have hroot : P.aeval x = 0 := by
    have h := congrArg (fun q : ℚ[X] => q.aeval x) hmap
    rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl,
      aeval_map_algebraMap,aeval_mul,aeval_C,hx,mul_zero] at h
    exact h
  have hlead : P.leadingCoeff = (sparseDenominator p : ℤ) := by
    have h := congrArg Polynomial.leadingCoeff hmap
    rw [Polynomial.leadingCoeff_map_of_injective (Int.castRingHom ℚ).injective_int,
      Polynomial.leadingCoeff_mul,Polynomial.leadingCoeff_C,hp.leadingCoeff,mul_one] at h
    change (P.leadingCoeff : ℚ) = (sparseDenominator p : ℚ) at h
    exact_mod_cast h
  have h := isIntegral_leadingCoeff_smul P x hroot
  simpa only [Algebra.smul_def,hlead,map_natCast] using h

/-- The literal sparse denominator programme handles repetitions, cancellation,
arbitrary term order and zero records; no canonical polynomial input is needed. -/
theorem sparse_root_coordinates_on_lattice (F : FixedField K n)
    (p : RationalPolynomialCode) (hp : p.polynomial.Monic)
    (x : K) (hx : p.polynomial.aeval x = 0) :
    ∀ i : Fin n, ∃ a : ℤ,
      F.basis.repr x i = (a : ℚ) /
        (coordinateLatticeDenominator F * sparseDenominator p : ℕ) :=
  coordinates_on_lattice F _ (sparseDenominator_pos p) x
    (sparseDenominator_integral_root p hp x hx)

end
end Paper2.ExactInput.FixedRootCodec
