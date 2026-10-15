import Paper2.SourceFaithful.Synthesis.MountainInterface
import Paper2.SourceFaithful.PublicHardness

/-! The manuscript's mountain interface for the literal public native-X
problem. The proved fixed-field hardness is transported by an executed
strict-root decoder for every correct polynomial-length oracle convention. -/
namespace Paper2.SourceFaithful.Synthesis
open Paper2.Tractable Paper2.ExactInput
noncomputable section

/-- Source Theorem 9.1 with the manuscript's strict public output convention.
The original finite language may contain zero and nullary rows. -/
theorem theorem_9_1_public
    (L : Language) {d : ℕ}
    (heven : ∀ f ∈ L.family, Even f.1)
    (hdiv : 3 ≤ d → ∀ f ∈ L.family, Tensor.HalfChargeDivisible f.2 d)
    (M : Signature AlgebraicComplex (2*d)) (hM : IsMountain M)
    (hmem : (⟨2*d,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ Problem.SharpPHard .nativeX L := by
  rcases theorem_9_1 L heven hdiv M hM hmem with ht | hh
  · exact Or.inl ht
  · exact Or.inr (public_hardness_of_fixed_field .nativeX L hh)

end
end Paper2.SourceFaithful.Synthesis

