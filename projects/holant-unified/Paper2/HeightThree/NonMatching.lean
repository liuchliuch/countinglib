import Paper2.HeightThree.FromRigidity
import Paper2.Certificates.Q6JointDeck
import Paper2.ExactInput.GadgetAugmentation

/-! Paper2 Theorem 7.5 from the complete finite Q6 cover, its actual
orbit naturality, and the source one-copy/two-copy native-X networks. -/
namespace Paper2.HeightThree
open Certificates.Q6 Tractable ExactInput Problem

theorem nonmatching_coordinate_mountain (F : SignatureFamily AlgebraicComplex)
    (a b : AlgebraicComplex) (q : Fin 20 → AlgebraicComplex) (hab : a*b ≠ 0)
    (hM : (⟨6,coordinateMountain a b q⟩ : AnySignature AlgebraicComplex) ∈ F) :
    ∃ h : Signature AlgebraicComplex 4, h ≠ 0 ∧ IsEO ⟨4,h⟩ ∧
      ¬ WeightedMatching.IsProduct h ∧ NetworkRealizable F h :=
  nonmatching_of_rigidity F a b q hab hM (joint_deck_support q (a*b) hab)

theorem nonmatching_mountain (F : SignatureFamily AlgebraicComplex)
    (M : Signature AlgebraicComplex 6) (hM : IsMountain (d := 3) M)
    (hmem : (⟨6,M⟩ : AnySignature AlgebraicComplex) ∈ F) :
    ∃ h : Signature AlgebraicComplex 4, h ≠ 0 ∧ IsEO ⟨4,h⟩ ∧
      ¬ WeightedMatching.IsProduct h ∧ NetworkRealizable F h := by
  apply nonmatching_coordinate_mountain F (M (fun _ => false)) (M (fun _ => true)) (mountainCoefficients M)
    (mul_ne_zero hM.zero_ne_zero hM.one_ne_zero)
  rw [← mountain_coordinate_decomposition M hM]
  exact hmem

/-- The promised output is adjoined to the original finite exact algebraic
language by an actual, length-controlled native-X graph reduction. -/
theorem adjoin_nonmatching_mountain (P : Paper1DirectGadgetAccepted) (L : Language)
    (M : Signature AlgebraicComplex 6) (hM : IsMountain (d := 3) M)
    (hmem : (⟨6,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ h : Signature AlgebraicComplex 4, ∃ A : Language,
      h ≠ 0 ∧ IsEO ⟨4,h⟩ ∧ ¬ WeightedMatching.IsProduct h ∧
      A.family = insert (⟨4,h⟩ : AnySignature AlgebraicComplex) L.family ∧
      Reduces .nativeX A L := by
  obtain ⟨h,hn,he,hm,hg⟩ := nonmatching_mountain L.family M hM hmem
  obtain ⟨A,hA,hr⟩ := P.adjoin_realizable L h hg
  exact ⟨h,A,hn,he,hm,hA,hr⟩

end Paper2.HeightThree
