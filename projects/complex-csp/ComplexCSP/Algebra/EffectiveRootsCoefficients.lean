import ComplexCSP.Algebra.EffectiveRootsExponent

/-!
# Runtime integer-coefficient ingress

The public executable routines use only a runtime dimension and the integer
tail of a monic polynomial. Native mathlib polynomials occur solely in semantic
proofs, since their constructors and ring operations lack executable code in
the pinned library.
-/

namespace ComplexCSP.EffectiveRoots

open scoped BigOperators Matrix

/-- Natural Cauchy bound read directly from the monic polynomial's integer tail. -/
def coefficientCauchyBound {n : ℕ} (a : Fin n → ℤ) : ℕ :=
  (∑ i, (a i).natAbs) + 1

def coefficientCompanion {n : ℕ} (a : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ if j.val + 1 = n then -(a i : ℚ) else if i.val = j.val + 1 then 1 else 0

def coefficientTraceGram {n : ℕ} (a : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ (coefficientCompanion a ^ (i.val + j.val)).trace

def coefficientRelation {n : ℕ} (a : Fin n → ℤ) : EncodedNumberField.CoeffVector n :=
  fun i ↦ -(a i : ℚ)

/-- Uniform executable root enumeration from raw integer coefficients. The
leading coefficient is implicitly one and the vector length is the degree. -/
def rootCoordinatesFromCoefficients (n : ℕ) (a : Fin n → ℤ) :
    Finset (EncodedNumberField.CoeffVector n) :=
  let C := candidateCoordinates (coefficientTraceGram a) (coefficientCauchyBound a)
  C.filter (fun v ↦ hasBoundedOrder (coefficientRelation a) C.card v = true)

/-- A literal list-input wrapper, with no native polynomial construction. -/
def rootCoordinatesFromList (a : List ℤ) : Finset (EncodedNumberField.CoeffVector a.length) :=
  rootCoordinatesFromCoefficients a.length a.get

/-- The even torsion exponent read from the computed finite root list. -/
def rootExponentFromCoefficients (n : ℕ) (a : Fin n → ℤ) : ℕ :=
  Nat.lcm 2 (rootCoordinatesFromCoefficients n a).card

theorem coefficientCauchyBound_eq {n : ℕ} (a : Fin n → ℤ) (p : Polynomial ℤ)
    (hdegree : p.natDegree = n) (hcoeff : ∀ i : Fin n, p.coeff i.val = a i) :
    coefficientCauchyBound a = integerCauchyBound p := by
  rw [integerCauchyBound, hdegree, Finset.sum_range]
  simp only [coefficientCauchyBound, hcoeff]

theorem coefficientCompanion_eq {n : ℕ} (a : Fin n → ℤ) (p : Polynomial ℤ)
    (hcoeff : ∀ i : Fin n, p.coeff i.val = a i) :
    coefficientCompanion a = companionMatrix n p := by
  ext i j
  simp only [coefficientCompanion, companionMatrix, hcoeff]

theorem coefficientTraceGram_eq {n : ℕ} (a : Fin n → ℤ) (p : Polynomial ℤ)
    (hcoeff : ∀ i : Fin n, p.coeff i.val = a i) :
    coefficientTraceGram a = gramFromPolynomial n p := by
  ext i j
  change (coefficientCompanion a ^ (i.val + j.val)).trace =
    (companionMatrix n p ^ (i.val + j.val)).trace
  rw [coefficientCompanion_eq a p hcoeff]

theorem coefficientRelation_eq {n : ℕ} (a : Fin n → ℤ) (p : Polynomial ℤ)
    (hcoeff : ∀ i : Fin n, p.coeff i.val = a i) :
    coefficientRelation a = relationCoordinates n p := by
  funext i
  simp only [coefficientRelation, relationCoordinates, hcoeff]

/-- The raw coefficient program is extensionally identical to the polynomial
semantic program, without constructing that polynomial at runtime. -/
theorem rootCoordinatesFromCoefficients_eq {n : ℕ} (a : Fin n → ℤ) (p : Polynomial ℤ)
    (hdegree : p.natDegree = n) (hcoeff : ∀ i : Fin n, p.coeff i.val = a i) :
    rootCoordinatesFromCoefficients n a = rootCoordinates n p := by
  simp only [rootCoordinatesFromCoefficients, rootCoordinates,
    coefficientTraceGram_eq a p hcoeff, coefficientCauchyBound_eq a p hdegree hcoeff,
    coefficientRelation_eq a p hcoeff]

variable {K : Type*} [Field K] [NumberField K]

theorem polynomial_natDegree_eq_dim (pb : PowerBasis ℚ K) (p : Polynomial ℤ)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen) : p.natDegree = pb.dim := by
  calc
    p.natDegree = (p.map (Int.castRingHom ℚ)).natDegree :=
      (Polynomial.natDegree_map_eq_of_injective Int.cast_injective p).symm
    _ = (minpoly ℚ pb.gen).natDegree := congrArg Polynomial.natDegree hpoly
    _ = pb.dim := pb.natDegree_minpoly

/-- Soundness and completeness for the actual raw-coefficient input API. -/
theorem mem_rootCoordinatesFromCoefficients_iff (pb : PowerBasis ℚ K)
    (p : Polynomial ℤ) (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen)
    (a : Fin pb.dim → ℤ) (hcoeff : ∀ i : Fin pb.dim, p.coeff i.val = a i)
    (v : EncodedNumberField.CoeffVector pb.dim) :
    v ∈ rootCoordinatesFromCoefficients pb.dim a ↔
      IsOfFinOrder (EncodedNumberField.interpret pb.gen v) := by
  rw [rootCoordinatesFromCoefficients_eq a p (polynomial_natDegree_eq_dim pb p hpoly) hcoeff]
  exact mem_rootCoordinates_iff pb p hp hroot hpoly v

theorem rootExponentFromCoefficients_ge_two (pb : PowerBasis ℚ K)
    (p : Polynomial ℤ) (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen)
    (a : Fin pb.dim → ℤ) (hcoeff : ∀ i : Fin pb.dim, p.coeff i.val = a i) :
    2 ≤ rootExponentFromCoefficients pb.dim a := by
  unfold rootExponentFromCoefficients
  rw [rootCoordinatesFromCoefficients_eq a p (polynomial_natDegree_eq_dim pb p hpoly) hcoeff]
  exact computedRootExponent_ge_two pb p hp hroot hpoly

/-- The even exponent needed by row detection is itself computable from the raw
integer input and is proved to kill every field root of unity. -/
theorem rootExponentFromCoefficients_killsTorsion (pb : PowerBasis ℚ K)
    (p : Polynomial ℤ) (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen)
    (a : Fin pb.dim → ℤ) (hcoeff : ∀ i : Fin pb.dim, p.coeff i.val = a i) :
    RowDetector.KillsTorsion K (rootExponentFromCoefficients pb.dim a) := by
  unfold rootExponentFromCoefficients
  rw [rootCoordinatesFromCoefficients_eq a p (polynomial_natDegree_eq_dim pb p hpoly) hcoeff]
  exact computedRootExponent_killsTorsion pb p hp hroot hpoly

end ComplexCSP.EffectiveRoots
