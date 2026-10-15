import Paper2.Paper1ProvedOddUnaryTernaryW
import Paper2.Paper1ProvedOddUnaryResidual
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange

/-! The ordinary-unary source selector now has exactly one remaining
mathematical case: an actual ordinary-isotropic W graph in a sourced table. -/
namespace Paper2.Paper1Proved.OddUnary
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

structure IsotropicWSource (L : Language) : Type 1 where
  source : TernarySource L
  residual : TernaryW.IsotropicWResidual source.K source.H

namespace TernarySource
variable {L : Language} (S : TernarySource L)

include S in
theorem hard_or_isotropic_w
    (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted) :
    FixedFieldOutput.SharpPHard .ordinary L ∨ Nonempty (IsotropicWSource L) := by
  let _ : Algebra ℚ S.K := S.K.algebra'
  let N : Macro S.H 3 := ⟨S.graph.network,S.graph.labels,S.graph.exact,S.graph.ordinary⟩
  let zeroPin : Macro S.H 1 := ⟨S.zeroPin.network,S.zeroPin.labels,S.zeroPin.exact,S.zeroPin.ordinary⟩
  have prime : Prime (⟨3,RingHomRealization.mapSignature S.K.subtype N.network.denote⟩ :
      Holant.AnySignature AlgebraicComplex) :=
    (prime_mapSignature_iff S.K.subtype _).mpr S.prime
  have pin : zeroPin.network.denote = fun x => S.scalar * QuaternaryUnaryAccess.pin false x := by
    funext x
    have hx : (fun _ : Fin 1 => x 0) = x := by
      funext i
      exact congrArg x (Fin.eq_zero i).symm
    rw [←hx]
    cases h : x 0
    · simpa [h,QuaternaryUnaryAccess.pin] using S.zeroPinFalse
    · simpa [h,QuaternaryUnaryAccess.pin] using S.zeroPinTrue
  rcases TernaryW.prime_hard_or_residual S.K S.F S.H L S.back P PG PR PF PN
      S.negative N prime zeroPin S.scalar S.scalarNonzero pin with hard | residual
  · exact Or.inl hard
  · exact Or.inr ⟨⟨S,residual⟩⟩
end TernarySource

namespace Source
variable (L : Language) (U : GeneralOddHighTerminalAccess.Actual (signatures L) 1)
variable (hn : GeneralOddNonisotropicFrame.norm U.graph.denote ≠ 0) (hnot : ¬ Tract L.family)

include hn hnot in
theorem hard_or_isotropic_w
    (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted) :
    FixedFieldOutput.SharpPHard .ordinary L ∨ Nonempty (IsotropicWSource L) := by
  rcases hard_or_ternary L U hn hnot P PG PR PF PN with hard | source
  · exact Or.inl hard
  · exact source.elim (fun S => S.hard_or_isotropic_w P PG PR PF PN)
end Source
end
end Paper2.Paper1Proved.OddUnary

