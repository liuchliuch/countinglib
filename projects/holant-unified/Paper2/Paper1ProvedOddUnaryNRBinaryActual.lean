import Paper2.Paper1ProvedOddUnaryNRBinarySlices
import Paper2.Paper1ProvedOddUnaryNRActualCaps

/-! The binary reconstruction consumes the two genuine ordinary dual caps.
Every coordinate slice is obtained with its exact nonzero cap scalar. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
noncomputable section
variable {K : Type} [Field K] {r : ℕ} {a : ℕ → ℕ}
variable {H : (i : Fin r) → Holant.Signature K (a i.val)}

theorem closed_binary_of_actual_caps (phi : K →+* AlgebraicComplex)
    (R : InvertibleKernel)
    (caps : Bool → NoXOrdinaryGraphAdjoin.Output H 1)
    (c : Bool → AlgebraicComplex) (cnz : ∀ b,c b≠0)
    (dual : ∀ b v,NR.columnPair
      (RingHomRealization.mapSignature phi (caps b).network.denote)
        R.matrix v=if v=b then c b else 0)
    (unaries : ∀ U : NoXOrdinaryGraphAdjoin.Output H 1,
      Closed (R.symm.action (RingHomRealization.mapSignature phi U.network.denote)))
    (N : NoXOrdinaryGraphAdjoin.Output H 2) :
    Closed (R.symm.action (RingHomRealization.mapSignature phi N.network.denote)) := by
  apply closed_binary_of_slices
  intro i b
  have hc := unaries (ActualCaps.output (caps b) N i)
  rw [ActualCaps.chart_denote phi R (caps b) b (c b) (dual b) N i] at hc
  exact (closed_scale_iff (c b) (cnz b) _).mp hc

end
end Paper2.Paper1Proved.OddUnary.NR

