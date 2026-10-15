import Paper2.Paper1ProvedOddUnarySource
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroPins
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinSelector

/-! The actual zero-origin branch supplies an ordinary two-pin table. Its
pure graph construction is reused, while its controlled source is composed
with the original ordinary Eq target and actual field-answer converter. -/
namespace Paper2.Paper1Proved.OddUnary.ZeroPins
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace Z
export GlobalCloseCompletionUnaryZeroPins
  (firstTable firstArity power vector ambientVector field presentation table arity family
   old_included pin_member pinLabel pin_literal power_form)
end Z
namespace A
export GlobalCloseCompletionIndependentPinsAdjoin (source)
end A
namespace P
export GlobalCloseCompletionUnaryPowerOrdinary (controlled)
export GlobalCloseCompletionUnaryPowerSource (graph exact ordinary value labels)
end P
namespace C
export GlobalCloseCompletionUnaryOrdinaryFieldCodec (ambient controlled)
end C
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
variable {r degree n : ℕ} {b : ℕ → ℕ}
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
local instance : CharZero K := Algebra.charZero_of_charZero ℚ K
variable (F : FixedField K degree) (H : (i : Fin r) → Holant.Signature K (b i.val))
variable (L : Language)
variable (back : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
  (sourceEncoding L) (GeneralOddHighTerminalAccess.presentation (signatures L)).encoding
  ((QuaternaryOrdinaryCompanion.tables F H).evaluate F)
  (GeneralOddHighTerminalAccess.targetValue (signatures L)))
variable (first : NoXOrdinaryGraphAdjoin.Output H 1) (c : K) (hc : c ≠ 0)
variable (h0 : first.network.denote (fun _ => false) = c)
variable (h1 : first.network.denote (fun _ => true) = 0)
variable (N : NoXOrdinaryGraphAdjoin.Output H n)
variable (hn : N.network.denote ≠ 0) (hz : N.network.denote (fun _ => false) = 0)

include back in
def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding ((r+1)+2) 1 (Z.arity K H first))
    (Z.presentation K F H first c).encoding
    (sourceEncoding L) (GeneralOddHighTerminalAccess.presentation (signatures L)).encoding
    ((QuaternaryOrdinaryCompanion.tables (Z.presentation K F H first c)
      (Z.table K F H first c)).evaluate (Z.presentation K F H first c))
    (GeneralOddHighTerminalAccess.targetValue (signatures L)) := by
  let E := Z.power K F H first c hc h0 h1 N hn hz
  let J := Z.firstTable K F H first c
  let cb := Programme.compose (A.source F H first c hc) back
  exact Programme.compose
    (P.controlled (C.ambient K J) (P.graph K E.graph) (P.labels K E.graph E.labels)
      (P.exact K J E.graph E.labels E.exact) (P.ordinary K E.graph E.edges)
      E.positive (fun v => (Z.vector K v : AlgebraicComplex)) (E.scalar : AlgebraicComplex)
      (by intro h;exact E.nonzero (Subtype.ext h))
      (P.value K E.graph (Z.vector K) E.scalar (Z.power_form K F H first c hc h0 h1 N hn hz)))
    (Programme.compose (C.controlled K F J) cb)

local instance : Algebra ℚ (Z.field K F H first c) := (Z.field K F H first c).algebra'
local instance : CharZero (Z.field K F H first c) :=
  Algebra.charZero_of_charZero ℚ (Z.field K F H first c)

def pin (v : Bool) : NoXOrdinaryGraphAdjoin.Output (Z.table K F H first c) 1 where
  network := Holant.Network.corolla (QuaternaryUnaryAccess.pin v)
  labels := {
    vertex _ := Z.pinLabel K F H first c hc h0 h1 v
    vertex_arity _ := congrArg Sigma.fst (Z.pin_literal K F H first c hc h0 h1 v)
    edge e := Fin.elim0 e }
  exact _ := Z.pin_literal K F H first c hc h0 h1 v
  ordinary e := Fin.elim0 e

theorem pin_value (v : Bool) :
    (pin K F H first c hc h0 h1 v).network.denote = QuaternaryUnaryAccess.pin v :=
  Holant.Network.denote_corolla _

theorem obstruction
    (negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H)) :
    ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient
      (Z.field K F H first c) (Z.table K F H first c)) :=
  fun ht => negative (ht.mono_family (Z.old_included K F H first c))

include back hc h0 h1 N hn hz in
theorem hard_or_ternary
    (P0 : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted)
    (negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H)) :
    FixedFieldOutput.SharpPHard .ordinary L ∨
      ∃ W : NoXOrdinaryGraphAdjoin.Output (Z.table K F H first c) 3,
        Holant.LocalDrafts.FinitePGL2.Stabilization.Prime
          (⟨3,W.network.denote⟩ : Holant.AnySignature (Z.field K F H first c)) := by
  have ht := obstruction K F H first c negative
  let pp := pin K F H first c hc h0 h1
  have pv := pin_value K F H first c hc h0 h1
  cases GlobalCloseCompletionUnaryBothPinSelector.produce
      (Z.field K F H first c) (Z.table K F H first c) pp pv ht with
  | ternary W prime => exact Or.inr ⟨W,prime⟩
  | paired D =>
    let pinMacro : OrdinaryNegativeCubicGadgets.Macro (Z.table K F H first c) 1 :=
      ⟨(pp false).network,(pp false).labels,(pp false).exact,(pp false).ordinary⟩
    let receipt := GlobalCloseCompletionPairedSeriesComplete.produce
      (Z.table K F H first c) (Z.presentation K F H first c)
      (Paired.complexEmbedding (Z.field K F H first c))
      D.graph D.matrix D.form D.nonsingular pinMacro 1 one_ne_zero
      (by rw [pv];simp [QuaternaryUnaryAccess.pin])
      (by rw [pv];simp [QuaternaryUnaryAccess.pin])
    exact Or.inl (receipt_hard (Z.field K F H first c) (Z.presentation K F H first c)
      (Z.table K F H first c) L (source K F H L back first c hc h0 h1 N hn hz)
      P0 PG PR PF PN ht receipt)

end
end Paper2.Paper1Proved.OddUnary.ZeroPins

