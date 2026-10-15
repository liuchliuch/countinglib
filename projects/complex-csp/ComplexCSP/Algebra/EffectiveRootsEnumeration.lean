import ComplexCSP.Algebra.EffectiveRootsPolynomial
import ComplexCSP.Algebra.EncodedNumberField

/-!
# Uniform executable root-of-unity enumeration from an integral presentation

The runtime algorithm takes only the dimension and integer polynomial. It
constructs a rational trace Gram matrix, its adjugate inverse, a finite integer
trace box, and rational coordinate candidates. It tests bounded orders in the
runtime coordinate algebra. No field, basis, embedding, or completeness oracle
occurs in the executable routine. A power basis and its minimal-polynomial
certificate appear only in the correctness proof.
-/

namespace ComplexCSP.EffectiveRoots

open scoped BigOperators

/-- The reduction coefficients for the monic polynomial relation. -/
def relationCoordinates (n : ℕ) (p : Polynomial ℤ) : EncodedNumberField.CoeffVector n :=
  fun i ↦ -(p.coeff i.val : ℚ)

/-- Force every coordinate once and retain a compact vector of values. This
prevents repeated function-coordinate lookup from expanding a power tree. -/
def materialize {n : ℕ} (a : EncodedNumberField.CoeffVector n) :
    EncodedNumberField.CoeffVector n :=
  let values := Vector.ofFn a
  fun i ↦ values[i.val]

@[simp] theorem materialize_eq {n : ℕ} (a : EncodedNumberField.CoeffVector n) :
    materialize a = a := by
  funext i
  simp [materialize]

/-- Recursive power state is actual vector data, so compiler arity reduction
cannot turn caching back into a re-evaluated function closure. -/
def powerVector {n : ℕ} (c : EncodedNumberField.CoeffVector n)
    (a : Vector ℚ n) : ℕ → Vector ℚ n
  | 0 => Vector.ofFn (EncodedNumberField.one n)
  | k + 1 =>
      let previous := powerVector c a k
      Vector.ofFn (EncodedNumberField.mul c (fun i ↦ previous[i.val]) (fun i ↦ a[i.val]))

theorem powerVector_ofFn {n : ℕ} (c a : EncodedNumberField.CoeffVector n) (k : ℕ) :
    powerVector c (Vector.ofFn a) k = Vector.ofFn (EncodedNumberField.pow c a k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [powerVector, ih, EncodedNumberField.pow]
    congr 1
    congr 1 <;> funext i <;> simp

/-- Natural powering with materialized intermediate coordinate vectors. -/
def materializedPow {n : ℕ} (c a : EncodedNumberField.CoeffVector n) (k : ℕ) :
    EncodedNumberField.CoeffVector n :=
  let result := powerVector c (Vector.ofFn a) k
  fun i ↦ result[i.val]

@[simp] theorem materializedPow_eq {n : ℕ} (c a : EncodedNumberField.CoeffVector n) (k : ℕ) :
    materializedPow c a k = EncodedNumberField.pow c a k := by
  funext i
  simp [materializedPow, powerVector_ofFn]

/-- Bounded exact testing of positive multiplicative order, performed only on
rational coordinate vectors. This avoids powering arbitrary candidates to N!. -/
def hasBoundedOrder {n : ℕ} (c : EncodedNumberField.CoeffVector n) (N : ℕ)
    (a : EncodedNumberField.CoeffVector n) : Bool :=
  let a := materialize a
  decide (∃ m : Fin N,
    EncodedNumberField.equal (materializedPow c a (m.val + 1))
      (EncodedNumberField.one n) = true)

/-- Uniform finite enumeration of roots of unity as rational coordinate vectors.
All computation is on the supplied integer polynomial and its runtime degree. -/
def rootCoordinates (n : ℕ) (p : Polynomial ℤ) : Finset (EncodedNumberField.CoeffVector n) :=
  let C := candidateCoordinates (gramFromPolynomial n p) (integerCauchyBound p)
  C.filter (fun a ↦ hasBoundedOrder (relationCoordinates n p) C.card a = true)

variable {K : Type*} [Field K] [NumberField K]

/-- A certified integral power-basis presentation satisfies the exact runtime
reduction relation. -/
theorem generator_relation (pb : PowerBasis ℚ K) (p : Polynomial ℤ)
    (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen) :
    pb.gen ^ pb.dim = EncodedNumberField.interpret pb.gen (relationCoordinates pb.dim p) := by
  have hdegree : p.natDegree = pb.dim := by
    calc
      p.natDegree = (p.map (Int.castRingHom ℚ)).natDegree :=
        (Polynomial.natDegree_map_eq_of_injective Int.cast_injective p).symm
      _ = (minpoly ℚ pb.gen).natDegree := congrArg Polynomial.natDegree hpoly
      _ = pb.dim := pb.natDegree_minpoly
  have hcoeff : p.coeff pb.dim = 1 := by
    rw [← hdegree, Polynomial.coeff_natDegree, hp.leadingCoeff]
  rw [Polynomial.aeval_eq_sum_range, hdegree, Finset.sum_range_succ, hcoeff, one_smul] at hroot
  simp only [zsmul_eq_mul] at hroot
  have hneg : pb.gen ^ pb.dim =
      -(∑ i ∈ Finset.range pb.dim, (p.coeff i : K) * pb.gen ^ i) :=
    eq_neg_of_add_eq_zero_right hroot
  rw [hneg, Finset.sum_range]
  simp only [EncodedNumberField.interpret, relationCoordinates, map_neg, map_intCast,
    neg_mul, Finset.sum_neg_distrib]

private theorem powerBasis_dim_pos (pb : PowerBasis ℚ K) : 0 < pb.dim := by
  rw [← pb.finrank]
  exact Module.finrank_pos

/-- Exact soundness and completeness of the runtime coordinate enumeration.
The argument contains no assumed root-enumeration completeness condition. -/
theorem mem_rootCoordinates_iff (pb : PowerBasis ℚ K) (p : Polynomial ℤ)
    (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen)
    (a : EncodedNumberField.CoeffVector pb.dim) :
    a ∈ rootCoordinates pb.dim p ↔ IsOfFinOrder (EncodedNumberField.interpret pb.gen a) := by
  let C := candidateCoordinates (gramFromPolynomial pb.dim p) (integerCauchyBound p)
  have hc := generator_relation pb p hp hroot hpoly
  have hn := powerBasis_dim_pos pb
  constructor
  · intro ha
    have hbounded := (Finset.mem_filter.mp ha).2
    unfold hasBoundedOrder at hbounded
    obtain ⟨m, hpow⟩ := of_decide_eq_true hbounded
    simp only [materializedPow_eq, materialize_eq] at hpow
    have heq := (EncodedNumberField.equal_iff_interpret pb _ _).mp hpow
    rw [EncodedNumberField.interpret_pow pb.gen _ _ hn hc,
      EncodedNumberField.interpret_one pb.gen hn] at heq
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m.val + 1, Nat.succ_pos _, heq⟩
  · intro ha
    apply Finset.mem_filter.mpr
    constructor
    · have hmem := root_coordinates_mem_computed_candidates pb p hp hroot hpoly
        (EncodedNumberField.interpret pb.gen a) ha
      simpa only [EncodedNumberField.coordinates_interpret] using hmem
    · unfold hasBoundedOrder
      apply decide_eq_true_eq.mpr
      have hbound := root_order_le_computed_candidate_card pb p hp hroot hpoly _ ha
      have hpos := ha.orderOf_pos
      refine ⟨⟨orderOf (EncodedNumberField.interpret pb.gen a) - 1, by omega⟩, ?_⟩
      simp only [materializedPow_eq, materialize_eq]
      apply (EncodedNumberField.equal_iff_interpret pb _ _).mpr
      rw [EncodedNumberField.interpret_pow pb.gen _ _ hn hc,
        EncodedNumberField.interpret_one pb.gen hn]
      change EncodedNumberField.interpret pb.gen a ^
        (orderOf (EncodedNumberField.interpret pb.gen a) - 1 + 1) = 1
      rw [Nat.sub_add_cancel hpos, pow_orderOf_eq_one]

/-- Every actual field root of unity is represented in the computed finite set. -/
theorem every_root_is_enumerated (pb : PowerBasis ℚ K) (p : Polynomial ℤ)
    (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen)
    (ζ : K) (hζ : IsOfFinOrder ζ) :
    ∃ a ∈ rootCoordinates pb.dim p, EncodedNumberField.interpret pb.gen a = ζ := by
  refine ⟨pb.basis.equivFun ζ, ?_, EncodedNumberField.interpret_coordinates pb ζ⟩
  apply (mem_rootCoordinates_iff pb p hp hroot hpoly _).mpr
  simpa only [EncodedNumberField.interpret_coordinates] using hζ

end ComplexCSP.EffectiveRoots
