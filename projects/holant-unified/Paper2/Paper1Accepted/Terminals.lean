import Paper2.ExactInput.GadgetAugmentation

/-! Exact source interfaces consumed by the new charge/matching routes.
Every field is a named, user-accepted Paper 1 result or its explicit §2.5
restriction convention. No Paper 2 relative-EO theorem is accepted here. -/
namespace Paper2
open Tractable ExactInput

/-- Literal subfamily restriction from Paper 1 §2.5's retained-enlargement
convention. The source and target are actual finite algebraic languages.
Its `Reduces` conclusion remains quantified over bounded target conventions;
it does not assert any general bounded-output existence. -/
structure Paper1RestrictionAccepted where
  restriction_2_5 : ∀ source target : Language, source.family ⊆ target.family →
    Problem.Reduces .nativeX source target

/-- Paper 1 Lemma 3.4, specialized to its literal-member unary case.
The conclusion classifies the full retained original language. -/
structure Paper1UnaryAccepted where
  unary_3_4 : ∀ L : Language, ∀ u : Signature AlgebraicComplex 1,
    u ≠ 0 → (⟨1, u⟩ : AnySignature AlgebraicComplex) ∈ L.family →
      Tract (kImage L) ∨ Problem.SharpPHard .nativeX L

/-- Paper 1 Theorem 2.16, the weighted-EO theorem restated as Paper 2
Theorem 2.11. The source is preprocessed and every member must actually be EO. This supplies no classification
of a non-EO ambient language merely containing an EO gadget. -/
structure Paper1EOAccepted where
  eo_2_16 : ∀ L : Language, Preprocessed L.family → (∀ g ∈ L.family, IsEO g) →
    (EOTract L.family → Problem.InFP .nativeX L) ∧
    (¬ EOTract L.family → Problem.SharpPHard .nativeX L)

namespace Paper1DirectGadgetAccepted

/-- Recover the exact reverse restriction promised by the source convention.
No unproved bound on arbitrary public root answers is inserted. -/
theorem adjoin_equivalence (P : Paper1DirectGadgetAccepted)
    (R : Paper1RestrictionAccepted) (L : Language) {n : ℕ}
    (f : Signature AlgebraicComplex n) (hf : NativeNetworkRealizesUpTo L.family f) :
    ∃ M : Language, M.family = insert (⟨n, f⟩ : AnySignature AlgebraicComplex) L.family ∧
      Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M := by
  obtain ⟨M, hM, hML⟩ := P.adjoin L f hf
  refine ⟨M, hM, hML, R.restriction_2_5 L M ?_⟩
  rw [hM]
  exact Set.subset_insert _ _

end Paper1DirectGadgetAccepted
end Paper2
