import Paper2.Paper1ProvedOddUnaryZeroPins

/-! All actual nonisotropic-unary exits are reduced to a genuine sourced
ternary. The source packet retains its actual ordinary graph, zero pin,
whole-family obstruction and controlled reduction; it asserts no classifier. -/
namespace Paper2.Paper1Proved.OddUnary
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

structure TernarySource (L : Language) : Type 1 where
  K : IntermediateField ℚ AlgebraicComplex
  degree : ℕ
  F : letI : Algebra ℚ K := K.algebra'; FixedField K degree
  count : ℕ
  arity : ℕ → ℕ
  H : (i : Fin count) → Holant.Signature K (arity i.val)
  back : letI : Algebra ℚ K := K.algebra'; LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) F.encoding
    (sourceEncoding L) (GeneralOddHighTerminalAccess.presentation (signatures L)).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F)
    (GeneralOddHighTerminalAccess.targetValue (signatures L))
  negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H)
  zeroPin : NoXOrdinaryGraphAdjoin.Output H 1
  scalar : K
  scalarNonzero : scalar ≠ 0
  zeroPinFalse : zeroPin.network.denote (fun _ => false) = scalar
  zeroPinTrue : zeroPin.network.denote (fun _ => true) = 0
  graph : NoXOrdinaryGraphAdjoin.Output H 3
  prime : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime
    (⟨3,graph.network.denote⟩ : Holant.AnySignature K)

namespace Source
variable (L : Language) (U : GeneralOddHighTerminalAccess.Actual (signatures L) 1)
variable (hn : GeneralOddNonisotropicFrame.norm U.graph.denote ≠ 0) (hnot : ¬ Tract L.family)
local instance : Algebra ℚ (field L) := (field L).algebra'

def ternary (N : NoXOrdinaryGraphAdjoin.Output (chartTable L U) 3)
    (hp : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime
      (⟨3,N.network.denote⟩ : Holant.AnySignature (field L))) : TernarySource L where
  K := field L
  degree := _
  F := presentation L
  count := L.count
  arity := L.arity
  H := chartTable L U
  back := chartBack L U hn
  negative := GlobalCloseCompletionUnaryFramedSelector.obstruction
    (field L) (table L) (first L U) (norm_nonzero L U hn) (negative L hnot)
  zeroPin := chartPin L U
  scalar := chartScalar L U
  scalarNonzero := GlobalCloseCompletionUnaryFramedSelector.scale_nonzero
    (field L) (table L) (first L U) (norm_nonzero L U hn)
  zeroPinFalse := GlobalCloseCompletionUnaryFramedSelector.pin0
    (field L) (table L) (first L U) (norm_nonzero L U hn)
  zeroPinTrue := GlobalCloseCompletionUnaryFramedSelector.pin1
    (field L) (table L) (first L U) (norm_nonzero L U hn)
  graph := N
  prime := hp

include hn hnot in
theorem hard_or_ternary
    (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted) :
    FixedFieldOutput.SharpPHard .ordinary L ∨ Nonempty (TernarySource L) := by
  rcases hard_or_residual L U hn hnot P PG PR PF PN with hh | ⟨N,hp⟩ | ⟨n,N,hN,hz,h0⟩
  · exact Or.inl hh
  · exact Or.inr ⟨ternary L U hn hnot N hp⟩
  · have hnorm := norm_nonzero L U hn
    have hc := GlobalCloseCompletionUnaryFramedSelector.scale_nonzero
      (field L) (table L) (first L U) hnorm
    have hf := GlobalCloseCompletionUnaryFramedSelector.pin0
      (field L) (table L) (first L U) hnorm
    have ht := GlobalCloseCompletionUnaryFramedSelector.pin1
      (field L) (table L) (first L U) hnorm
    have hneg := GlobalCloseCompletionUnaryFramedSelector.obstruction
      (field L) (table L) (first L U) hnorm (negative L hnot)
    let J := chartTable L U
    let pin := chartPin L U
    let c := chartScalar L U
    rcases ZeroPins.hard_or_ternary (field L) (presentation L) J L (chartBack L U hn)
      pin c hc hf ht N hz h0 P PG PR PF PN hneg with hard | ⟨W,hp⟩
    · exact Or.inl hard
    · let K := ZeroPins.Z.field (field L) (presentation L) J pin c
      let _ : Algebra ℚ K := K.algebra'
      let pp := ZeroPins.pin (field L) (presentation L) J pin c hc hf ht
      have pv := ZeroPins.pin_value (field L) (presentation L) J pin c hc hf ht
      exact Or.inr ⟨{
        K := K
        degree := _
        F := ZeroPins.Z.presentation (field L) (presentation L) J pin c
        count := (L.count+1)+2
        arity := ZeroPins.Z.arity (field L) J pin
        H := ZeroPins.Z.table (field L) (presentation L) J pin c
        back := ZeroPins.source (field L) (presentation L) J L (chartBack L U hn)
          pin c hc hf ht N hz h0
        negative := ZeroPins.obstruction (field L) (presentation L) J pin c hneg
        zeroPin := pp false
        scalar := 1
        scalarNonzero := one_ne_zero
        zeroPinFalse := by rw [pv];simp [QuaternaryUnaryAccess.pin]
        zeroPinTrue := by rw [pv];simp [QuaternaryUnaryAccess.pin]
        graph := W
        prime := hp }⟩

end Source
end
end Paper2.Paper1Proved.OddUnary

