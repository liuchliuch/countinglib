import Paper2.HeightOne.Dihedral.HighArityOrder
import Holant.Dihedral.CompatibleCoefficientLine.TensorFactor

/-! A family of complete matching coefficient tables with no two distinct
factor-line discrepancies has a literal common binary factor. Zero sampled
cards are retained: their complementary factor is exactly zero. -/
namespace Paper2.HeightOne.Dihedral.HighArity
noncomputable section
open Holant.Marked
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Pairwise Hamming distance at most one in projective factor lines forces
one common line once the matching has at least two edges. -/
theorem common_projective_factor {I : Type*} {r : ℕ} (hr : 2 ≤ r)
    (A : I → Fin r → Mat) (i₀ : I)
    (hp : ∀ i j (e f : Fin r),e ≠ f →
      ProjectivelyEqual (A i e) (A j e) ∨ ProjectivelyEqual (A i f) (A j f)) :
    ∃ e : Fin r,∀ i,ProjectivelyEqual (A i e) (A i₀ e) := by
  classical
  by_cases ha : ∀ i e,ProjectivelyEqual (A i e) (A i₀ e)
  · exact ⟨⟨0,by omega⟩,fun i => ha i _⟩
  push_neg at ha
  obtain ⟨i₁,e,he⟩ := ha
  obtain ⟨f,hf⟩ : ∃ f : Fin r,f ≠ e := by
    by_cases h : e = ⟨0,by omega⟩
    · refine ⟨⟨1,by omega⟩,?_⟩
      rw [h]
      intro hh
      have := congrArg Fin.val hh
      simp at this
    · exact ⟨⟨0,by omega⟩,Ne.symm h⟩
  have h₁ : ProjectivelyEqual (A i₁ f) (A i₀ f) :=
    (hp i₁ i₀ e f (Ne.symm hf)).resolve_left he
  refine ⟨f,fun i => ?_⟩
  by_contra hi
  have hei : ProjectivelyEqual (A i e) (A i₀ e) :=
    (hp i i₀ e f (Ne.symm hf)).resolve_right hi
  rcases hp i i₁ e f (Ne.symm hf) with h | h
  · exact he (h.symm.trans hei)
  · exact hi (h.trans h₁)

end
end Paper2.HeightOne.Dihedral.HighArity
