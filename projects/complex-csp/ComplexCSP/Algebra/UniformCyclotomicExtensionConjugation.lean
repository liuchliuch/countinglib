import ComplexCSP.Algebra.UniformCyclotomicExtensionSearch
import ComplexCSP.Algebra.EncodedNumberFieldInverse
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Executable conjugation coordinates in the searched extension

The old complex realization extends along any accepted field embedding. This
matters: its chosen conjugation need not commute with every other embedding.
-/
namespace ComplexCSP.AlgebraicEncoding
open EncodedNumberField
open scoped BigOperators

/-- Cross-dimension rational polynomial substitution. -/
def evaluateCoordinates {n r : ℕ} (relation a : CoeffVector n)
    (v : CoeffVector r) : CoeffVector n :=
  ∑ i : Fin r, v i • EncodedNumberField.pow relation a i.val

/-- Runtime conjugate-generator coordinates, using the old conjugate coordinates
and inverse of the newly adjoined root. -/
def extensionConjugateCoordinates {n r : ℕ} (relation a b : CoeffVector n)
    (oldConjugate : CoeffVector r) (d : ℕ) (m : ℤ) : CoeffVector n :=
  add ((d : ℚ) • evaluateCoordinates relation a oldConjugate)
    ((m : ℚ) • inverse relation b)

 theorem interpret_evaluateCoordinates
    {K : Type*} [Field K] [Algebra ℚ K] {n r : ℕ}
    (α : K) (relation a : CoeffVector n) (v : CoeffVector r)
    (hn : 0 < n) (hc : α ^ n = interpret α relation) :
    interpret α (evaluateCoordinates relation a v) = interpret (interpret α a) v := by
  unfold evaluateCoordinates
  rw [interpret_sum]
  change (∑ i, interpret α (v i • EncodedNumberField.pow relation a i.val)) =
    ∑ i, algebraMap ℚ K (v i) * interpret α a ^ i.val
  simp only [interpret_smul, interpret_pow α relation a hn hc]

 theorem map_interpret {K E : Type*} [Field K] [Field E] [Algebra ℚ K] [Algebra ℚ E]
    (φ : K →+* E) {n : ℕ} (α : K) (v : CoeffVector n) :
    φ (interpret α v) = interpret (φ α) v := by
  simp [interpret]

/-- Every specified old complex embedding extends to the candidate number field. -/
theorem exists_complex_embedding_extension
    {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E]
    (ψ : K →+* E) (φ : K →+* ℂ) :
    ∃ Φ : E →+* ℂ, Φ.comp ψ = φ := by
  letI : Algebra K E := ψ.toAlgebra
  letI : Algebra K ℂ := φ.toAlgebra
  let Φ : E →ₐ[K] ℂ := IsAlgClosed.lift
  refine ⟨Φ.toRingHom, ?_⟩
  ext x
  exact Φ.commutes x

/-- Correctness of the computable conjugate-generator vector in any compatible
complex realization of the old generator and root. -/
theorem extensionConjugateCoordinates_correct
    {E : Type} [Field E] [NumberField E]
    (pb : PowerBasis ℚ E) (relation a b : CoeffVector pb.dim)
    (hc : pb.gen ^ pb.dim = interpret pb.gen relation)
    {r : ℕ} (oldConjugate : CoeffVector r) (d : ℕ) (m : ℤ)
    (hg : pb.gen = (d : E) * interpret pb.gen a + (m : E) * interpret pb.gen b)
    (δ : ℕ) (hδ : 0 < δ) (hb : IsPrimitiveRoot (interpret pb.gen b) δ)
    (Φ : E →+* ℂ)
    (hold : interpret (Φ (interpret pb.gen a)) oldConjugate = star (Φ (interpret pb.gen a))) :
    interpret (Φ pb.gen) (extensionConjugateCoordinates relation a b oldConjugate d m) =
      star (Φ pb.gen) := by
  rw [← map_interpret]
  simp only [extensionConjugateCoordinates, interpret_add, interpret_smul,
    interpret_evaluateCoordinates _ _ _ _ pb.dim_pos hc, interpret_inverse pb relation b hc, map_natCast, map_intCast]
  change Φ ((d : E) * interpret (interpret pb.gen a) oldConjugate +
    (m : E) * (interpret pb.gen b)⁻¹) = _
  rw [conjugate_generator_formula Φ (interpret pb.gen a) (interpret pb.gen b)
    (interpret (interpret pb.gen a) oldConjugate) d m hδ hb
    (by rw [map_interpret]; exact hold), ← hg]

end ComplexCSP.AlgebraicEncoding
