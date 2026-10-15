import Paper2.TransversalCube
import Paper2.ExactInput.PublicRootBound

/-! Full original-language hardness conclusion of Lemma 7.2. The public
root-answer bound is now a proved theorem for every literal language. -/
namespace Paper2.TransversalCube
open Tractable ExactInput
open scoped BigOperators

variable {n : ℕ}

theorem matching_mountain_hard
    (DG : Paper1DirectGadgetAccepted) (R : Paper1RestrictionAccepted) (EO : Paper1EOAccepted)
    (L : Language) (P : WeightedMatching.Pairing n) (hd : 3 ≤ P.count)
    (a b c : AlgebraicComplex) (p q : Fin P.count → AlgebraicComplex) (hab : a*b ≠ 0)
    (hcoeff : c * ∏ j, p j * q j ≠ 0)
    (hM : (⟨n, sourceMountain P a b c p q⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Problem.SharpPHard .nativeX L :=
  matching_mountain_hard_of_bounded DG R EO L P hd a b c p q hab hcoeff hM
    (boundedAnswers_nonempty .nativeX L)

end Paper2.TransversalCube
