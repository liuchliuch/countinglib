import Paper2.SourceFaithful.Synthesis.OriginalMountainRoute
import Paper2.SourceFaithful.HeightTwo
import Paper2.SourceFaithful.HeightThree.Complete

/-! Section 9 mountain case assembly.

The height-two and height-three conclusions are proved in this project.  This
module makes the remaining height-one and height-at-least-four obligations
visible as actual original-language mountain routes.  Neither an abstract
classification oracle nor a new accepted Paper 2 theorem is introduced.
-/
namespace Paper2.SourceFaithful.Synthesis
open Tractable ExactInput Problem

/-- A remaining branch of the genuine Section 9 preparation.  In either
constructor, the retained language has a real mountain, its post-factor gcd,
all-even arities and charge divisibility, and an actual reduction back to the
original language.  The record contains no assumed complexity conclusion. -/
inductive RemainingMountainRoute (L : Language) : Type where
  | heightOne (route : OriginalMountainRoute L)
      (height_eq_one : route.prepared.height = 1) : RemainingMountainRoute L
  | heightAtLeastFour (route : OriginalMountainRoute L)
      (height_ge_four : 4 ≤ route.prepared.height) : RemainingMountainRoute L

/-- The two complete local classifications discharge heights two and three.
The other cases retain the full preparation rather than substituting a desired
terminal conclusion for its missing proof. -/
theorem original_hard_or_remaining_mountain
    (P : Paper1Accepted) (PO : Paper1OddAccepted) (PE : Paper1EOAccepted)
    (PS : Paper1SingleWeightAccepted) (PD : Paper1DirectGadgetAccepted)
    (PF : Paper1FactorClosureAccepted) (PR : Paper1RestrictionAccepted)
    (PU : Paper1UnaryAccepted) (PN : Paper1NormalizationAccepted)
    (PC : Paper1OccurrenceAccepted)
    (L : Language) (hnot : ¬ Tract (kImage L)) :
    FixedFieldOutput.SharpPHard .nativeX L ∨ Nonempty (RemainingMountainRoute L) := by
  classical
  rcases original_hard_or_gcd_mountain PO PE PS PD PF PR PU L hnot with hh | hA
  · exact Or.inl hh
  obtain ⟨A⟩ := hA
  have hd : 0 < A.prepared.height := A.prepared.isMountain.height_pos
  by_cases h1 : A.prepared.height = 1
  · exact Or.inr ⟨RemainingMountainRoute.heightOne A h1⟩
  by_cases h2 : A.prepared.height = 2
  · have classify : ∀ (d : ℕ) (M : Signature AlgebraicComplex (2 * d)),
        d = 2 → IsMountain M →
        (⟨2 * d,M⟩ : AnySignature AlgebraicComplex) ∈ A.prepared.language.family →
        Tract (kImage A.prepared.language) ∨
          FixedFieldOutput.SharpPHard .nativeX A.prepared.language := by
      intro d M hd hM hmem
      subst d
      exact HeightTwo.mountain_classification_preprocessed P PF PN A.prepared.language
        A.prepared.preprocessed M hmem hM
    rcases classify A.prepared.height A.prepared.mountain h2
      A.prepared.isMountain A.prepared.member with ht | hh
    · exact False.elim (A.nontractable hnot ht)
    · exact Or.inl (A.transfer_hardness hh)
  by_cases h3 : A.prepared.height = 3
  · have classify : ∀ (d : ℕ) (M : Signature AlgebraicComplex (2 * d)),
        d = 3 → (∀ f ∈ A.prepared.language.family,
          Tensor.HalfChargeDivisible f.2 (d : ℤ)) → IsMountain M →
        (⟨2 * d,M⟩ : AnySignature AlgebraicComplex) ∈ A.prepared.language.family →
        Tract (kImage A.prepared.language) ∨
          FixedFieldOutput.SharpPHard .nativeX A.prepared.language := by
      intro d M hd hdiv hM hmem
      subst d
      exact HeightThree.theorem_7_1 PD PC PF PU PE PR A.prepared.language
        A.prepared.even (by simpa using hdiv) M hM hmem
    rcases classify A.prepared.height A.prepared.mountain h3 A.prepared.divisible
      A.prepared.isMountain A.prepared.member with ht | hh
    · exact False.elim (A.nontractable hnot ht)
    · exact Or.inl (A.transfer_hardness hh)
  exact Or.inr ⟨RemainingMountainRoute.heightAtLeastFour A (by omega)⟩

/-- Transparent conditional Section 9 completion.  The only Paper 2 premises
are displayed as the precise two missing height theorems; this result must not
be reported as an unconditional classification until both premises have proved
values.  All other mountain preparation and height cases are actually proved. -/
theorem native_hardness_of_remaining_height_theorems
    (P : Paper1Accepted) (PO : Paper1OddAccepted) (PE : Paper1EOAccepted)
    (PS : Paper1SingleWeightAccepted) (PD : Paper1DirectGadgetAccepted)
    (PF : Paper1FactorClosureAccepted) (PR : Paper1RestrictionAccepted)
    (PU : Paper1UnaryAccepted) (PN : Paper1NormalizationAccepted)
    (PC : Paper1OccurrenceAccepted)
    (height_one : ∀ L : Language, Preprocessed L.family →
      (∀ f ∈ L.family, Even f.1) →
      ∀ M : Signature AlgebraicComplex 2, IsMountain (d := 1) M →
      (⟨2, M⟩ : AnySignature AlgebraicComplex) ∈ L.family →
        Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L)
    (height_at_least_four : ∀ L : Language, Preprocessed L.family →
      ∀ d : ℕ, 4 ≤ d → (∀ f ∈ L.family, Even f.1) →
      (∀ f ∈ L.family, Tensor.HalfChargeDivisible f.2 d) →
      ∀ M : Signature AlgebraicComplex (2 * d), IsMountain M →
      (⟨2 * d, M⟩ : AnySignature AlgebraicComplex) ∈ L.family →
        Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L)
    (L : Language) (hnot : ¬ Tract (kImage L)) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  rcases original_hard_or_remaining_mountain P PO PE PS PD PF PR PU PN PC L hnot with
    hh | hremaining
  · exact hh
  obtain ⟨remaining⟩ := hremaining
  cases remaining with
  | heightOne A h1 =>
    have classify : ∀ (d : ℕ) (M : Signature AlgebraicComplex (2 * d)),
        d = 1 → IsMountain M →
        (⟨2 * d,M⟩ : AnySignature AlgebraicComplex) ∈ A.prepared.language.family →
        Tract (kImage A.prepared.language) ∨
          FixedFieldOutput.SharpPHard .nativeX A.prepared.language := by
      intro d M hd hM hmem
      subst d
      exact height_one A.prepared.language A.prepared.preprocessed A.prepared.even
        M hM hmem
    rcases classify A.prepared.height A.prepared.mountain h1
      A.prepared.isMountain A.prepared.member with ht | hh
    · exact False.elim (A.nontractable hnot ht)
    · exact A.transfer_hardness hh
  | heightAtLeastFour A h4 =>
    rcases height_at_least_four A.prepared.language A.prepared.preprocessed
      A.prepared.height h4 A.prepared.even A.prepared.divisible
      A.prepared.mountain A.prepared.isMountain A.prepared.member with ht | hh
    · exact False.elim (A.nontractable hnot ht)
    · exact A.transfer_hardness hh

end Paper2.SourceFaithful.Synthesis
