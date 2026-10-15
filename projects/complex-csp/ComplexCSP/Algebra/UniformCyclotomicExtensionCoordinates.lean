import ComplexCSP.Algebra.UniformCyclotomicExtension
import ComplexCSP.Algebra.EncodedNumberField
import Mathlib.Analysis.Complex.Basic

/-!
# Rational-coordinate witnesses and sound embeddings

These proofs expose exactly the finite coordinates sought by a cyclotomic
extension search. The mathematical field is used only to prove existence and
soundness, never to execute candidate tests.
-/
namespace ComplexCSP.AlgebraicEncoding

open Polynomial IntermediateField EncodedNumberField

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E]

/-- Any tested root of the old presentation polynomial gives a genuine field embedding. -/
noncomputable def embeddingOfRoot (old : IntegralPrimitivePresentation K)
    (a : E) (ha : aeval a (old.polynomial.map (Int.castRingHom ℚ)) = 0) : K →ₐ[ℚ] E :=
  old.basis.lift a (old.map_eq_minpoly ▸ ha)

@[simp] theorem embeddingOfRoot_gen (old : IntegralPrimitivePresentation K)
    (a : E) (ha : aeval a (old.polynomial.map (Int.castRingHom ℚ)) = 0) :
    embeddingOfRoot old a ha old.basis.gen = a :=
  old.basis.lift_gen a _

/-- The generator test rules out unrelated superfields: the two tested elements
really generate the complete candidate field. -/
theorem adjoin_pair_top_of_generator (pb : PowerBasis ℚ E) (a b : E)
    (d : ℕ) (m : ℤ) (hg : pb.gen = (d : E) * a + (m : E) * b) :
    ℚ⟮a, b⟯ = ⊤ := by
  have ha : a ∈ ℚ⟮a, b⟯ := subset_adjoin ℚ _ (by simp)
  have hb : b ∈ ℚ⟮a, b⟯ := subset_adjoin ℚ _ (by simp)
  have hn : (d : E) ∈ ℚ⟮a, b⟯ := ℚ⟮a, b⟯.natCast_mem d
  have hm : (m : E) ∈ ℚ⟮a, b⟯ := ℚ⟮a, b⟯.intCast_mem m
  have hgen : pb.gen ∈ ℚ⟮a, b⟯ := by
    rw [hg]
    exact add_mem (mul_mem hn ha) (mul_mem hm hb)
  apply top_unique
  rw [← adjoin_eq_top_of_algebra ℚ _ pb.adjoin_gen_eq_top]
  exact adjoin_simple_le_iff.mpr hgen

/-- A fully finite rational-coordinate witness exists for each positive root order. -/
theorem exists_cyclotomic_coordinate_witness
    (old : IntegralPrimitivePresentation K) (δ : ℕ) (hδ : 0 < δ) :
    ∃ (P : IntegralPrimitivePresentation (CyclotomicExtension K δ))
      (a b : CoeffVector P.basis.dim) (d : ℕ) (m : ℤ),
      0 < d ∧
      interpret P.basis.gen a = algebraMap K (CyclotomicExtension K δ) old.basis.gen ∧
      aeval (interpret P.basis.gen a) (old.polynomial.map (Int.castRingHom ℚ)) = 0 ∧
      IsPrimitiveRoot (interpret P.basis.gen b) δ ∧
      P.basis.gen = (d : CyclotomicExtension K δ) * interpret P.basis.gen a +
        (m : _) * interpret P.basis.gen b := by
  obtain ⟨ζ, d, m, hζ, hd, hi, hg⟩ := exists_cyclotomic_integral_generator K old δ hδ
  let E := CyclotomicExtension K δ
  let α : E := (d : E) * algebraMap K E old.basis.gen + (m : E) * ζ
  let P := integralPresentationOfPrimitive α hi hg
  let a := P.basis.basis.equivFun (algebraMap K E old.basis.gen)
  let b := P.basis.basis.equivFun ζ
  have ha : interpret P.basis.gen a = algebraMap K E old.basis.gen :=
    interpret_coordinates P.basis _
  have hb : interpret P.basis.gen b = ζ := interpret_coordinates P.basis _
  refine ⟨P, a, b, d, m, hd, ha, ?_, hb ▸ hζ, ?_⟩
  · rw [ha, old.map_eq_minpoly, aeval_algebraMap_apply, minpoly.aeval, map_zero]
  · rw [ha, hb]
    exact integralPresentationOfPrimitive_gen α hi hg

omit [NumberField E] in
/-- Complex conjugation of a finite-order element is its inverse. -/
theorem star_image_primitiveRoot (φ : E →+* ℂ) {b : E} {δ : ℕ}
    (hδ : 0 < δ) (hb : IsPrimitiveRoot b δ) : star (φ b) = φ b⁻¹ := by
  rw [map_inv₀]
  apply (Complex.inv_eq_conj _).symm
  exact (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨δ, hδ, by rw [← map_pow, hb.pow_eq_one, map_one]⟩).norm_eq_one

/-- The searched linear combination gives the conjugate-generator formula
without an additional conjugation oracle for the new field. -/
theorem conjugate_generator_formula (φ : E →+* ℂ) (a b ac : E)
    (d : ℕ) (m : ℤ) {δ : ℕ} (hδ : 0 < δ) (hb : IsPrimitiveRoot b δ)
    (hac : φ ac = star (φ a)) :
    φ ((d : E) * ac + (m : E) * b⁻¹) =
      star (φ ((d : E) * a + (m : E) * b)) := by
  simp only [map_add, map_mul, map_natCast, map_intCast, star_add, star_mul,
    star_natCast, star_intCast, hac, star_image_primitiveRoot φ hδ hb]
  ring

end ComplexCSP.AlgebraicEncoding
