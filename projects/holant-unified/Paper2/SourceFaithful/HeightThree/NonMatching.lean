import Paper2.HeightThree.NonMatching
import Paper2.SourceFaithful.LocalInputs

/-! The actual Theorem 7.5 network is reused unchanged. Its finite augmentation
is proved against the source-faithful canonical number-field answer convention.
No old strict-root reduction or answer conversion is consumed. -/
namespace Paper2.SourceFaithful.HeightThree
open Tractable ExactInput

 theorem adjoin_nonmatching_mountain (P : Paper1DirectGadgetAccepted) (L : Language)
    (M : Signature AlgebraicComplex 6) (hM : IsMountain (d := 3) M)
    (hmem : (⟨6,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ h : Signature AlgebraicComplex 4, ∃ A : Language,
      h ≠ 0 ∧ IsEO ⟨4,h⟩ ∧ ¬ WeightedMatching.IsProduct h ∧
      A.family = insert (⟨4,h⟩ : AnySignature AlgebraicComplex) L.family ∧
      FixedFieldOutput.Reduces .nativeX A L := by
  obtain ⟨h,hn,he,hm,hg⟩ := Paper2.HeightThree.nonmatching_mountain L.family M hM hmem
  obtain ⟨A,hA,hr⟩ := P.adjoin_realizable L h hg
  exact ⟨h,A,hn,he,hm,hA,hr⟩

end Paper2.SourceFaithful.HeightThree
