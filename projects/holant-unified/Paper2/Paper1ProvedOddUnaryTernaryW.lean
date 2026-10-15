import Paper2.Paper1ProvedOddUnaryTernaryGHZ
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZScalarPinSource
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsTernaryRankOne
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsSymmetricDecomposition
import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZSource

/-! Ordinary triangles genuinely close the W cases with a nonzero repeated
column pairing. The remaining three zero pairings are recorded explicitly. -/
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
set_option maxRecDepth 16384

namespace TernaryW
namespace W
export GlobalCloseCompletionIndependentPinsWGeneralCore
  (image gram triangle_image gram_determinant core_basis)
end W
namespace G
export GlobalCloseCompletionTernaryGHZGraph (triangle value)
export GlobalCloseCompletionTernaryGHZSource (rotate rotate_value map_triangle)
end G
namespace Forms
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz)
end Forms
namespace ScalarPin
export GlobalCloseCompletionSymmetricGHZScalarPinSource
  (table pin pin_value source lift lift_value included)
end ScalarPin

section Pure
variable {K : Type} [Field K] {r : ℕ} {b : ℕ → ℕ}
variable {H : (i : Fin r) → Holant.Signature K (b i.val)}

theorem good_triangle (phi : K →+* AlgebraicComplex) (N : Macro H 3)
    (A B C : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote = W.image A.matrix B.matrix C.matrix)
    (good : W.gram (1 : AlgebraicComplex) B.matrix C.matrix false false ≠ 0) :
    ∃ Q : Holant.Tractable.InvertibleKernel,
      RingHomRealization.mapSignature phi (G.triangle N).network.denote = Forms.ghz Q.matrix := by
  have det : W.gram (1 : AlgebraicComplex) B.matrix C.matrix false false * W.gram 1 B.matrix C.matrix true true -
      W.gram 1 B.matrix C.matrix false true * W.gram 1 B.matrix C.matrix true false ≠ 0 := by
    rw [W.gram_determinant,one_mul]
    exact mul_ne_zero (Holant.Tractable.SymmetricBinaryPullback.determinant_ne_zero B)
      (Holant.Tractable.SymmetricBinaryPullback.determinant_ne_zero C)
  obtain ⟨Q,hQ⟩ := W.core_basis _ _ _ _ good det
  refine ⟨A.comp Q,?_⟩
  rw [G.value,G.map_triangle,form]
  have one : GlobalCloseCompletionIndependentPinsWCore.twist (1 : AlgebraicComplex)
      (W.image A.matrix B.matrix C.matrix) = W.image A.matrix B.matrix C.matrix := by
    funext x
    simp [GlobalCloseCompletionIndependentPinsWCore.twist,GlobalCloseCompletionIndependentPinsWCore.sign]
  rw [←one,W.triangle_image,←GlobalCloseCompletionIndependentPinsWCore.coordinate,hQ]
  exact Holant.Signature.coordinateAction_comp _ _ _

theorem rotate_image (phi : K →+* AlgebraicComplex) (N : Macro H 3)
    (A B C : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote = W.image A.matrix B.matrix C.matrix) :
    RingHomRealization.mapSignature phi (G.rotate N).network.denote = W.image C.matrix A.matrix B.matrix := by
  funext x
  rw [RingHomRealization.mapSignature,G.rotate_value]
  have h := congrFun form (GlobalCloseCompletionTernaryGHZCore.cyclic x)
  change phi (N.network.denote (GlobalCloseCompletionTernaryGHZCore.cyclic x)) = _ at h
  rw [h]
  simp [W.image,GlobalCloseCompletionTernaryGHZCore.cyclic]
  ring

theorem good_output (phi : K →+* AlgebraicComplex) (N : Macro H 3)
    (A B C : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote = W.image A.matrix B.matrix C.matrix)
    (good : W.gram (1 : AlgebraicComplex) B.matrix C.matrix false false ≠ 0 ∨
      W.gram 1 A.matrix B.matrix false false ≠ 0 ∨ W.gram 1 C.matrix A.matrix false false ≠ 0) :
    ∃ out : Macro H 3, ∃ Q : Holant.Tractable.InvertibleKernel,
      RingHomRealization.mapSignature phi out.network.denote = Forms.ghz Q.matrix := by
  rcases good with bc | ab | ca
  · obtain ⟨Q,hQ⟩ := good_triangle phi N A B C form bc
    exact ⟨G.triangle N,Q,hQ⟩
  · obtain ⟨Q,hQ⟩ := good_triangle phi (G.rotate N) C A B (rotate_image phi N A B C form) ab
    exact ⟨G.triangle (G.rotate N),Q,hQ⟩
  · have first := rotate_image phi N A B C form
    have second := rotate_image phi (G.rotate N) C A B first
    obtain ⟨Q,hQ⟩ := good_triangle phi (G.rotate (G.rotate N)) B C A second ca
    exact ⟨G.triangle (G.rotate (G.rotate N)),Q,hQ⟩
end Pure

variable {r degree : ℕ} {b : ℕ → ℕ}
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
variable (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
variable (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
variable (PN : SourceFaithful.Paper1NormalizationAccepted)

include back P PG PR PF PN in
theorem scalar_symmetric_ghz_hard
    (negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (N : Macro H 3) (pin0 : Macro H 1) (c : K) (hc : c ≠ 0)
    (M : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature K.subtype N.network.denote = Forms.ghz M.matrix)
    (pin : pin0.network.denote = fun x => c * QuaternaryUnaryAccess.pin false x) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  let J := ScalarPin.table K F H pin0 c
  have hn : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K J) :=
    fun ht => negative (ht.mono_family (ScalarPin.included K F H pin0 c))
  have hf : RingHomRealization.mapSignature K.subtype (ScalarPin.lift K F H pin0 c N).network.denote =
      Forms.ghz M.matrix := form
  exact TernaryGHZ.symmetric_ghz_hard K F J L (Programme.compose (ScalarPin.source K F H pin0 c hc) back)
    P PG PR PF PN hn (ScalarPin.lift K F H pin0 c N) (ScalarPin.pin K F H pin0 c hc pin)
    M hf (ScalarPin.pin_value K F H pin0 c hc pin)

/-- This residual is the actual same-table W graph, including all three
vanishing ordinary repeated-column pairings. -/
def IsotropicWResidual : Prop := ∃ N : Macro H 3, ∃ A B C : Holant.Tractable.InvertibleKernel,
  RingHomRealization.mapSignature K.subtype N.network.denote = W.image A.matrix B.matrix C.matrix ∧
  W.gram (1 : AlgebraicComplex) B.matrix C.matrix false false = 0 ∧
  W.gram 1 A.matrix B.matrix false false = 0 ∧ W.gram 1 C.matrix A.matrix false false = 0

include back P PG PR PF PN in
theorem w_hard_or_residual
    (negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (N : Macro H 3) (pin0 : Macro H 1) (c : K) (hc : c ≠ 0)
    (pin : pin0.network.denote = fun x => c * QuaternaryUnaryAccess.pin false x)
    (A B C : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature K.subtype N.network.denote = W.image A.matrix B.matrix C.matrix) :
    FixedFieldOutput.SharpPHard .ordinary L ∨ IsotropicWResidual K H := by
  classical
  by_cases good : W.gram (1 : AlgebraicComplex) B.matrix C.matrix false false ≠ 0 ∨
      W.gram 1 A.matrix B.matrix false false ≠ 0 ∨ W.gram 1 C.matrix A.matrix false false ≠ 0
  · obtain ⟨out,Q,hQ⟩ := good_output K.subtype N A B C form good
    exact Or.inl (scalar_symmetric_ghz_hard K F H L back P PG PR PF PN negative out pin0 c hc Q hQ pin)
  · have bad := not_or.mp good
    exact Or.inr ⟨N,A,B,C,form,not_ne_iff.mp bad.1,not_ne_iff.mp (not_or.mp bad.2).1,
      not_ne_iff.mp (not_or.mp bad.2).2⟩

include back P PG PR PF PN in
/-- Every genuine prime ternary is consumed, except for the explicit
ordinary-isotropic W residual. No trace-zero binary is assumed. -/
theorem prime_hard_or_residual
    (negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (N : Macro H 3) (prime : Prime
      (⟨3,RingHomRealization.mapSignature K.subtype N.network.denote⟩ : Holant.AnySignature AlgebraicComplex))
    (pin0 : Macro H 1) (c : K) (hc : c ≠ 0)
    (pin : pin0.network.denote = fun x => c * QuaternaryUnaryAccess.pin false x) :
    FixedFieldOutput.SharpPHard .ordinary L ∨ IsotropicWResidual K H := by
  rcases GlobalCloseCompletionIndependentPinsTernaryRankOne.decomposition _ prime with
    ⟨A,B,C,form⟩ | ⟨A,B,C,form⟩
  · obtain ⟨out,primeOut,v,hv⟩ := GlobalCloseCompletionTernaryGHZSource.produce K.subtype N A B C form prime
    have values : GlobalCloseCompletionTernaryGHZSymmetry.values
        (GlobalCloseCompletionTernaryGHZSymmetry.symmetric v) = v := by
      funext i
      fin_cases i <;> rfl
    have symmetry : RingHomRealization.mapSignature K.subtype out.network.denote =
        GlobalCloseCompletionTernaryGHZSymmetry.symmetric
          (GlobalCloseCompletionTernaryGHZSymmetry.values (RingHomRealization.mapSignature K.subtype out.network.denote)) := by
      rw [hv,values]
    rcases GlobalCloseCompletionIndependentPinsSymmetricDecomposition.symmetric_prime _ symmetry primeOut with
      ⟨R,hR⟩ | ⟨R,hR⟩
    · exact Or.inl (scalar_symmetric_ghz_hard K F H L back P PG PR PF PN negative out pin0 c hc R hR pin)
    · have formW : RingHomRealization.mapSignature K.subtype out.network.denote = W.image R.matrix R.matrix R.matrix := by
        rw [hR]
        exact (GlobalCloseCompletionIndependentPinsWCore.image_eq R.matrix).symm
      exact w_hard_or_residual K F H L back P PG PR PF PN negative out pin0 c hc pin R R R formW
  · exact w_hard_or_residual K F H L back P PG PR PF PN negative N pin0 c hc pin A B C form

end TernaryW
end
end Paper2.Paper1Proved.OddUnary

