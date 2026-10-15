import Paper2.Paper1ProvedOddUnaryTernarySymmetricWNormalized
import Paper2.Paper1ProvedOddUnaryTernaryResidual

/-! The remaining ordinary-unary source packet supplies a genuine symmetric
isotropic W graph over the same finite dictionary and the same source field. -/
namespace Paper2.Paper1Proved.OddUnary
open Paper2.ExactInput
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace IsotropicWSource
variable {L : Language} (S : IsotropicWSource L)

theorem symmetric_graph :
    ∃ N : Macro S.source.H 3, ∃ R : Holant.Tractable.InvertibleKernel, ∃ delta : AlgebraicComplex,
      delta ≠ 0 ∧ R.matrix false false ≠ 0 ∧ R.matrix true false ≠ 0 ∧
      R.matrix false false ^ 2 + R.matrix true false ^ 2 = 0 ∧
      RingHomRealization.mapSignature S.source.K.subtype N.network.denote =
        (fun x => delta * GlobalCloseCompletionIndependentPinsWCore.image R.matrix x) := by
  obtain ⟨N,A,B,C,form,bc,ab,ca⟩ := S.residual
  let pin : Macro S.source.H 1 :=
    ⟨S.source.zeroPin.network,S.source.zeroPin.labels,S.source.zeroPin.exact,S.source.zeroPin.ordinary⟩
  have hc : S.source.K.subtype S.source.scalar ≠ 0 :=
    S.source.K.subtype.injective.ne S.source.scalarNonzero
  have zeroPin : RingHomRealization.mapSignature S.source.K.subtype pin.network.denote =
      (fun x => if x 0 then 0 else S.source.K.subtype S.source.scalar) := by
    funext x
    have hx : (fun _ : Fin 1 => x 0) = x := by
      funext i
      exact congrArg x (Fin.eq_zero i).symm
    change S.source.K.subtype (pin.network.denote x) = _
    rw [←hx]
    cases h : x 0
    · simpa [pin,h] using congrArg S.source.K.subtype S.source.zeroPinFalse
    · simpa [pin,h] using congrArg S.source.K.subtype S.source.zeroPinTrue
  obtain ⟨R,delta,hd,columns,iso,output⟩ := TernaryW.isotropic_symmetric_output S.source.K.subtype
    N pin (S.source.K.subtype S.source.scalar) hc A B C form zeroPin bc ab ca
  obtain ⟨a0,a1,-,-⟩ := TernaryW.common_isotropic_line A B C bc ab ca
  exact ⟨TernaryW.symmetricGraph N pin,R,delta,hd,by simpa [columns] using a0,
    by simpa [columns] using a1,by simpa [columns] using iso,output⟩

end IsotropicWSource
end
end Paper2.Paper1Proved.OddUnary

