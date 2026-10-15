import Paper2.Paper1ProvedOddUnaryAdjacent
import Paper2.RelativeEO.GeneralizedEqualityGadget
import Paper2.HeightTwo

/-! The two small arities of an extracted weighted generalized equality
have direct exits: arity one has nonzero ordinary K-chart norm, and arity
two is the literal nonsingular diagonal table. -/
namespace Paper2.Paper1Proved.OddUnary.GeneralizedEqualitySmall
open Paper2.Tractable Paper2.ExactInput
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
noncomputable section

theorem one_norm (a b : AlgebraicComplex) :
    GeneralOddNonisotropicFrame.norm (Holant.Tractable.sourceKBasis.action
      (RelativeEO.generalizedEquality (n := 1) a b))=2*a*b := by
  rw [Adjacent.ordinary_norm]
  simp [RelativeEO.generalizedEquality,funext_iff,Fin.forall_fin_succ]

theorem one_norm_ne_zero (a b : AlgebraicComplex) (ha : a≠0) (hb : b≠0) :
    GeneralOddNonisotropicFrame.norm (Holant.Tractable.sourceKBasis.action
      (RelativeEO.generalizedEquality (n := 1) a b))≠0 := by
  rw [one_norm]
  exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hb

theorem two_weightedEquality (a b : AlgebraicComplex) (ha : a≠0) (hb : b≠0) :
    HeightTwo.WeightedEquality (RelativeEO.generalizedEquality (n := 2) a b) := by
  simp [HeightTwo.WeightedEquality,RelativeEO.generalizedEquality,
    funext_iff,Fin.forall_fin_succ,ha,hb]

end
end Paper2.Paper1Proved.OddUnary.GeneralizedEqualitySmall
