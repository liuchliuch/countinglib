import Paper2.Paper1ProvedOddUnaryIsotropicGeneralizedEqualityStage
import Paper2.Paper1ProvedOddUnaryGeneralizedEqualityNormalize
import Paper2.DegreeCSP.EqualityHardness

/-! Every retained weighted generalized equality of arity at least three has
an unconditional canonical counting consumer. Genuine diagonal normalization
retains literal equality and both unit pins, and the all-degree BO theorem
supplies hardness with the original controlled oracle reductions. -/
namespace Paper2.Paper1Proved.OddUnary.IsotropicGeneralizedEqualityStage
open Tractable ExactInput
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem GeneralizedEqualitySource.hard {L : Language}
    (S : GeneralizedEqualitySource L) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  obtain ⟨t,ht,M,_,_,heq,h0,h1,_,htract,hback,_⟩ :=
    GeneralizedEqualityNormalize.normalized S.retained.language S.retained.preprocessed
      (by have h:=S.arityAtLeastThree;omega) S.first S.second
      S.firstNonzero S.secondNonzero (NativeNetworkRealizesUpTo.of_realizable S.graph)
      S.retained.pinZero S.retained.pinOne
  have hid : DegreeCSP.equality S.arity=GeneralizedEqualityNormalize.equality S.arity := by
    funext x
    exact DegreeCSP.equality_eq S.arity x
  rw [←hid] at heq
  have hnotM : ¬Tract (familyAction sourceKBasis M.family) := by
    intro hM
    exact S.retained.nontractable (htract hM)
  have hM := DegreeCSP.EqualityHardness.hard M S.arity S.arityAtLeastThree
    heq h0 h1 hnotM
  exact S.transfer_hard (hM.transport hback)

end
end Paper2.Paper1Proved.OddUnary.IsotropicGeneralizedEqualityStage
