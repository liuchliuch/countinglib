import ComplexCSP.Algebra.UniformCyclotomicExtensionCoordinates
import ComplexCSP.Algebra.MonicIrreducibility
import ComplexCSP.Algebra.EffectiveRootsCoefficients
import Mathlib.Logic.Encodable.Pi
import Mathlib.Data.Rat.Encodable

/-!
# Executable candidate tests for a cyclotomic extension

The candidate consists solely of finite integer/rational data. Polynomial
operations and semantic models occur only in correctness proofs.
-/
namespace ComplexCSP.AlgebraicEncoding
open Polynomial EncodedNumberField
open scoped BigOperators

/-- A monic integer polynomial evaluated using runtime rational coordinates. -/
def evaluateMonicTail {n r : ℕ} (relation : CoeffVector n)
    (p : Fin r → ℤ) (a : CoeffVector n) : CoeffVector n :=
  ∑ i : Fin (r + 1), ((MonicIrreducibility.fromTail p i : ℤ) : ℚ) •
    EncodedNumberField.pow relation a i.val

/-- Generator coordinates remain correct also when the field degree is one. -/
def generatorCoordinates {n : ℕ} (relation : CoeffVector n) : CoeffVector n :=
  shift relation (one n)

/-- Exact order is a bounded power computation, including order one. -/
def primitiveRootTest {n : ℕ} (relation a : CoeffVector n) (δ : ℕ) : Bool :=
  decide (0 < δ ∧ equal (EncodedNumberField.pow relation a δ) (one n) = true ∧
    ∀ k : Fin δ, 0 < k.val → equal (EncodedNumberField.pow relation a k.val) (one n) = false)

/-- Polynomial tail, old-generator coordinates, root coordinates, d, and m. -/
abbrev CyclotomicCandidate := Σ n : ℕ,
  (Fin n → ℤ) × CoeffVector n × CoeffVector n × ℕ × ℤ

namespace CyclotomicCandidate
abbrev dimension (C : CyclotomicCandidate) := C.1
abbrev tail (C : CyclotomicCandidate) := C.2.1
abbrev oldGenerator (C : CyclotomicCandidate) := C.2.2.1
abbrev root (C : CyclotomicCandidate) := C.2.2.2.1
abbrev d (C : CyclotomicCandidate) := C.2.2.2.2.1
abbrev m (C : CyclotomicCandidate) := C.2.2.2.2.2

def relation (C : CyclotomicCandidate) : CoeffVector C.dimension :=
  EffectiveRoots.coefficientRelation C.tail

def test {r : ℕ} (old : Fin r → ℤ) (δ : ℕ) (C : CyclotomicCandidate) : Bool :=
  decide (0 < C.dimension ∧ 0 < C.d ∧
    MonicIrreducibility.irreducibleMonicTail C.tail = true ∧
    equal (evaluateMonicTail C.relation old C.oldGenerator) (zero C.dimension) = true ∧
    primitiveRootTest C.relation C.root δ = true ∧
    equal (generatorCoordinates C.relation)
      (add ((C.d : ℚ) • C.oldGenerator) ((C.m : ℚ) • C.root)) = true)

end CyclotomicCandidate

section Correctness
variable {K : Type*} [Field K] [Algebra ℚ K] {n r : ℕ}

 theorem interpret_evaluateMonicTail (α : K) (relation : CoeffVector n)
    (p : Fin r → ℤ) (a : CoeffVector n) (hn : 0 < n)
    (hc : α ^ n = interpret α relation) :
    interpret α (evaluateMonicTail relation p a) =
      aeval (interpret α a) (MonicIrreducibility.denote (MonicIrreducibility.fromTail p)) := by
  unfold evaluateMonicTail MonicIrreducibility.denote
  rw [interpret_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [interpret_smul, interpret_pow α relation a hn hc, aeval_monomial]
  simp

 theorem interpret_generatorCoordinates (α : K) (relation : CoeffVector n)
    (hn : 0 < n) (hc : α ^ n = interpret α relation) :
    interpret α (generatorCoordinates relation) = α := by
  rw [generatorCoordinates, interpret_shift α relation _ hc, interpret_one α hn, mul_one]

 theorem primitiveRootTest_correct (pb : PowerBasis ℚ K) (relation a : CoeffVector pb.dim)
    (hc : pb.gen ^ pb.dim = interpret pb.gen relation) (δ : ℕ) (hδ : 0 < δ) :
    primitiveRootTest relation a δ = true ↔ IsPrimitiveRoot (interpret pb.gen a) δ := by
  have eqpow (k : ℕ) : equal (EncodedNumberField.pow relation a k) (one pb.dim) = true ↔
      interpret pb.gen a ^ k = 1 := by
    rw [equal_iff_interpret pb, interpret_pow _ _ _ pb.dim_pos hc, interpret_one _ pb.dim_pos]
  have nepow (k : ℕ) : equal (EncodedNumberField.pow relation a k) (one pb.dim) = false ↔
      interpret pb.gen a ^ k ≠ 1 := by
    exact Bool.eq_false_iff.trans (not_congr (eqpow k))
  simp only [primitiveRootTest, decide_eq_true_eq, hδ, true_and, eqpow, nepow]
  constructor
  · rintro ⟨hp, hlt⟩
    exact IsPrimitiveRoot.mk_of_lt _ hδ hp (fun k hk hkδ => hlt ⟨k, hkδ⟩ hk)
  · intro h
    exact ⟨h.pow_eq_one, fun k hk => h.pow_ne_one_of_pos_of_lt (ne_of_gt hk) k.isLt⟩

/-- The complete finite test agrees with the intended equations in any actual
power-basis model of the candidate polynomial. -/
theorem candidateTest_correct_in_model (pb : PowerBasis ℚ K)
    (q : Fin pb.dim → ℤ) (a b : CoeffVector pb.dim) (d : ℕ) (m : ℤ)
    (old : Fin r → ℤ) (δ : ℕ) (hδ : 0 < δ)
    (hc : pb.gen ^ pb.dim = interpret pb.gen (EffectiveRoots.coefficientRelation q)) :
    CyclotomicCandidate.test old δ ⟨pb.dim, q, a, b, d, m⟩ = true ↔
      0 < d ∧ MonicIrreducibility.irreducibleMonicTail q = true ∧
      aeval (interpret pb.gen a) (MonicIrreducibility.denote (MonicIrreducibility.fromTail old)) = 0 ∧
      IsPrimitiveRoot (interpret pb.gen b) δ ∧
      pb.gen = (d : K) * interpret pb.gen a + (m : K) * interpret pb.gen b := by
  simp only [CyclotomicCandidate.test, decide_eq_true_eq,
    CyclotomicCandidate.dimension, CyclotomicCandidate.tail, CyclotomicCandidate.oldGenerator,
    CyclotomicCandidate.root, CyclotomicCandidate.d, CyclotomicCandidate.m,
    CyclotomicCandidate.relation, pb.dim_pos, true_and]
  rw [equal_iff_interpret pb, interpret_evaluateMonicTail _ _ _ _ pb.dim_pos hc,
    interpret_zero, primitiveRootTest_correct pb _ _ hc δ hδ,
    equal_iff_interpret pb, interpret_generatorCoordinates _ _ pb.dim_pos hc,
    interpret_add, interpret_smul, interpret_smul]
  simp

end Correctness

/-- The semantic existence theorem supplies all data accepted by the runtime
checker, including actual validation of the new irreducible polynomial. -/
theorem exists_accepted_cyclotomic_candidate
    {K : Type} [Field K] [NumberField K]
    (old : IntegralPrimitivePresentation K) (p : Fin old.basis.dim → ℤ)
    (hp : ∀ i, old.polynomial.coeff i.val = p i) (δ : ℕ) (hδ : 0 < δ) :
    ∃ C : CyclotomicCandidate, C.test p δ = true := by
  obtain ⟨P, a, b, d, m, hd, _, hroot, hb, hgen⟩ :=
    exists_cyclotomic_coordinate_witness old δ hδ
  let q : Fin P.basis.dim → ℤ := fun i => P.polynomial.coeff i.val
  have hqroot : aeval P.basis.gen P.polynomial = 0 := by
    rw [← aeval_map_algebraMap ℚ]
    change aeval P.basis.gen (P.polynomial.map (Int.castRingHom ℚ)) = 0
    rw [P.map_eq_minpoly, minpoly.aeval]
  have hc : P.basis.gen ^ P.basis.dim =
      interpret P.basis.gen (EffectiveRoots.coefficientRelation q) := by
    rw [EffectiveRoots.coefficientRelation_eq q P.polynomial (fun _ => rfl)]
    exact EffectiveRoots.generator_relation P.basis P.polynomial P.monic hqroot P.map_eq_minpoly
  refine ⟨⟨P.basis.dim, q, a, b, d, m⟩, ?_⟩
  apply (candidateTest_correct_in_model P.basis q a b d m p δ hδ hc).mpr
  refine ⟨hd, ?_, ?_, hb, hgen⟩
  · apply (MonicIrreducibility.irreducibleMonicTail_correct_of_coeff q P.polynomial P.monic
      (EffectiveRoots.polynomial_natDegree_eq_dim P.basis P.polynomial P.map_eq_minpoly)
      (fun _ => rfl)).mpr
    rw [P.map_eq_minpoly]
    exact minpoly.irreducible P.basis.isIntegral_gen
  · rw [MonicIrreducibility.denote_fromTail_eq p old.polynomial old.monic
      (EffectiveRoots.polynomial_natDegree_eq_dim old.basis old.polynomial old.map_eq_minpoly) hp]
    rw [← aeval_map_algebraMap ℚ]
    exact hroot

/-- Natural-number enumeration of all finite candidate records. -/
def cyclotomicCandidateFromCode (code : ℕ) : CyclotomicCandidate :=
  (Encodable.decode (α := CyclotomicCandidate) code).getD
    ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, 0, 0⟩

@[simp] theorem cyclotomicCandidateFromCode_encode (C : CyclotomicCandidate) :
    cyclotomicCandidateFromCode (Encodable.encode C) = C := by
  simp [cyclotomicCandidateFromCode]

theorem exists_accepted_cyclotomic_code
    {K : Type} [Field K] [NumberField K]
    (old : IntegralPrimitivePresentation K) (p : Fin old.basis.dim → ℤ)
    (hp : ∀ i, old.polynomial.coeff i.val = p i) (δ : ℕ) (hδ : 0 < δ) :
    ∃ code : ℕ, (cyclotomicCandidateFromCode code).test p δ = true := by
  obtain ⟨C, hC⟩ := exists_accepted_cyclotomic_candidate old p hp δ hδ
  exact ⟨Encodable.encode C, by simpa using hC⟩
end ComplexCSP.AlgebraicEncoding
