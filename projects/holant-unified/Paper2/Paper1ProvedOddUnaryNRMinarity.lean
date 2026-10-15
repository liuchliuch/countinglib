import Paper2.Paper1ProvedOddUnaryNRWholeFamily
import Paper2.Paper1ProvedOddUnaryNRActualCaps

/-! A genuine least outside graph has arity at most three once the two
actual dual caps are present. The whole-family version constructs its
outside source internally and keeps all old graph labels and coefficients. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {r : ℕ} {a : ℕ → ℕ}
variable {K : IntermediateField ℚ AlgebraicComplex}
variable {H : (i : Fin r) → Holant.Signature K (a i.val)}
variable {R : Holant.Tractable.InvertibleKernel}

namespace CoordinateMinimum

/-- Minimum arity rules out every high-arity graph using a proved physical
one-cap descendant in the same original table and the same NR chart. -/
theorem arity_le_three (M : CoordinateMinimum K H R)
    (caps : Bool → NoXOrdinaryGraphAdjoin.Output H 1)
    (c : Bool → AlgebraicComplex) (cnz : ∀ b,c b≠0)
    (dual : ∀ b v,NR.columnPair
      (RingHomRealization.mapSignature K.subtype (caps b).network.denote)
        R.matrix v=if v=b then c b else 0) : M.arity≤3 := by
  rcases M with ⟨m,positive,N,outside,least⟩
  cases m with
  | zero => omega
  | succ n =>
    by_contra bound
    change ¬(n+1≤3) at bound
    have large : 4≤n+1 := by omega
    obtain ⟨i,b,failure⟩ := ActualCaps.exists_outside_cap
      (K := K) (r := r) (a := a) (H := H) (n := n)
      K.subtype R caps c cnz dual N large outside
    have lower := least n (ActualCaps.output (caps b) N i) failure
    omega
end CoordinateMinimum

/-- Original whole-family negativity yields an actual unary, binary, or
ternary exit. No outside-class hypothesis is supplied by the caller. -/
theorem whole_family_small_coordinates
    (iso : R.matrix false false^2+R.matrix true false^2=0)
    (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (caps : Bool → NoXOrdinaryGraphAdjoin.Output H 1)
    (c : Bool → AlgebraicComplex) (cnz : ∀ b,c b≠0)
    (dual : ∀ b v,NR.columnPair
      (RingHomRealization.mapSignature K.subtype (caps b).network.denote)
        R.matrix v=if v=b then c b else 0) :
    ∃ n,0<n ∧ n≤3 ∧ ∃ N : NoXOrdinaryGraphAdjoin.Output H n,
      ¬Closed (R.symm.action (RingHomRealization.mapSignature K.subtype N.network.denote)) := by
  obtain ⟨M⟩ := whole_family_coordinate_minimum K H R iso negative
  exact ⟨M.arity,M.positive,M.arity_le_three caps c cnz dual,M.graph,M.outside⟩

end
end Paper2.Paper1Proved.OddUnary.NR

