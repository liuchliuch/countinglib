import Paper2.Paper1ProvedOddUnaryJordanTraceZeroPins
import Paper2.Paper1ProvedOddUnaryTernaryGHZ
import Paper2.Paper1ProvedProvider
import Paper2.Paper1ProvedGadgetProvider
import Paper2.Paper1ProvedRestrictionProvider
import Paper2.Paper1ProvedFactorProvider
import Paper2.Paper1ProvedNormalizationProvider
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsResourceTernary

/-! The literal two-pin and symmetric trace-zero table closes at the unchanged
ordinary oracle. We use the actual symmetric GHZ graph constructed by the
proved independent-pin terminal, then the canonical Paper 1 equality criterion.
The final query alphabet therefore consists of the original ordinary rows.
-/
namespace Paper2.Paper1Proved.OddUnary.JordanBothPinHardness
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace T
export GlobalCloseCompletionSymmetricGHZTrace (binary)
end T
namespace U
export GlobalCloseCompletionUnaryTraceOrX (Witness)
end U

variable {r degree : ℕ} {a : ℕ → ℕ}
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
local instance : CharZero K := Algebra.charZero_of_charZero ℚ K
variable (F : FixedField K degree)
variable (H : (i : Fin r) → Holant.Signature K (a i.val))

/-- The trace witness is obtained from one literal row over the original
coefficient field. Its coefficients are mapped by the same field inclusion. -/
def trace_witness (j : Fin r) (diagonal offDiagonal : K)
    (literal : (⟨a j.val,H j⟩ : Holant.AnySignature K) =
      ⟨2,T.binary diagonal offDiagonal offDiagonal⟩)
    (nonsingular : -diagonal^2-offDiagonal^2 ≠ 0) :
    U.Witness (GlobalCloseCompletionUnaryDescentSource.ambient K H) := by
  have member : (⟨2,T.binary (diagonal : AlgebraicComplex)
      (offDiagonal : AlgebraicComplex) (offDiagonal : AlgebraicComplex)⟩ :
      Holant.AnySignature AlgebraicComplex) ∈
        GlobalCloseCompletionUnaryDescentSource.ambient K H := by
    refine ⟨j,?_⟩
    refine (congrArg (RingHomRealization.mapAny K.subtype) literal).trans ?_
    apply congrArg (fun f : Holant.Signature AlgebraicComplex 2 =>
      (⟨2,f⟩ : Holant.AnySignature AlgebraicComplex))
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [RingHomRealization.mapSignature,T.binary,h0,h1] <;> rfl
  have determinant : -(diagonal : AlgebraicComplex)^2-
      (offDiagonal : AlgebraicComplex)*(offDiagonal : AlgebraicComplex) ≠ 0 := by
    intro hz
    apply nonsingular
    apply Subtype.ext
    change -(diagonal : AlgebraicComplex)^2-(offDiagonal : AlgebraicComplex)^2 = 0
    simpa only [pow_two] using hz
  exact .trace diagonal offDiagonal member determinant

variable (L : Language)
variable (back : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 a) F.encoding
  (sourceEncoding L) (GeneralOddHighTerminalAccess.presentation (signatures L)).encoding
  ((QuaternaryOrdinaryCompanion.tables F H).evaluate F)
  (GeneralOddHighTerminalAccess.targetValue (signatures L)))

include F back in
/-- The independent-pin construction produces an actual GHZ graph using
the complete retained table. The proved Paper 1 providers then close its
canonical ordinary hardness and the controlled back programme. -/
theorem ternary_hard
    (negative : ¬ Holant.Tractable.Tract
      (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (N : NoXOrdinaryGraphAdjoin.Output H 3)
    (prime : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime
      (⟨3,N.network.denote⟩ : Holant.AnySignature K))
    (p : Bool → Fin r)
    (hp : ∀ b, (⟨a (p b).val,H (p b)⟩ : Holant.AnySignature K) =
      ⟨1,QuaternaryUnaryAccess.pin b⟩)
    (j : Fin r) (diagonal offDiagonal : K)
    (literal : (⟨a j.val,H j⟩ : Holant.AnySignature K) =
      ⟨2,T.binary diagonal offDiagonal offDiagonal⟩)
    (nonsingular : -diagonal^2-offDiagonal^2 ≠ 0) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  let resource := trace_witness K H j diagonal offDiagonal literal nonsingular
  let out := GlobalCloseCompletionIndependentPinsResourceTernary.fromOutput
    K H N prime resource
  let pin0 : Macro H 1 := Macro.row (p false) (QuaternaryUnaryAccess.pin false) (hp false)
  exact TernaryGHZ.symmetric_ghz_hard K F H L back
    Paper2.Paper1Proved.provider Paper2.Paper1Proved.directGadgetProvider
    Paper2.Paper1Proved.restrictionProvider Paper2.Paper1Proved.factorProvider
    Paper2.Paper1Proved.normalizationProvider negative out.resource pin0
    out.basis out.form (Macro.row_denote _ _ _)

end
end Paper2.Paper1Proved.OddUnary.JordanBothPinHardness

namespace Paper2.Paper1Proved.OddUnary.JordanTraceZeroPins.Packet
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {L : Paper2.ExactInput.Language} (S : TernarySource L)

/-- The packet retains the source's actual prime ternary and whole-family
obstruction. All new rows return through its literal controlled programme. -/
theorem hard
    (D : letI : Algebra ℚ S.K := S.K.algebra';
      letI : CharZero S.K := Algebra.charZero_of_charZero ℚ S.K;
      JordanTraceZeroPins.Packet S.F S.H) :
    Paper2.FixedFieldOutput.SharpPHard .ordinary L := by
  let : Algebra ℚ S.K := S.K.algebra'
  let : CharZero S.K := Algebra.charZero_of_charZero ℚ S.K
  exact JordanBothPinHardness.ternary_hard S.K S.F D.signatures L
    (Programme.compose D.back S.back)
    (RetainedTable.negative S.K D.old D.old_literal S.negative)
    (RetainedTable.lift D.old D.old_literal S.graph) S.prime
    D.p D.hp D.traceLabel D.diagonal D.offDiagonal D.trace_literal D.nonsingular

end
end Paper2.Paper1Proved.OddUnary.JordanTraceZeroPins.Packet

