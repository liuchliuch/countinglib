import Paper2.Paper1ProvedOddUnaryTernaryW
import Paper2.Paper1ProvedOddUnaryTernaryLine
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsWGraph

/-! A genuine nonsingular ordinary binary that breaks the repeated W line
is inserted on one port. The resulting ordinary triangle is symmetric GHZ. -/
namespace Paper2.Paper1Proved.OddUnary.TernaryW
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

namespace D
export GlobalCloseCompletionIndependentPinsWGraph (decorate order)
end D
namespace Transpose
export GlobalCloseCompletionEq4CommonBasis (transpose)
end Transpose

def column_pairing (T B C : Holant.Kernel AlgebraicComplex) : AlgebraicComplex :=
  B false false * (T false false * C false false + T false true * C true false) +
    B true false * (T true false * C false false + T true true * C true false)

theorem gram_after (T B C : Holant.Tractable.InvertibleKernel) :
    W.gram (1 : AlgebraicComplex) ((Transpose.transpose T).comp B).matrix C.matrix false false =
      column_pairing T.matrix B.matrix C.matrix := by
  simp only [W.gram,Holant.Tractable.InvertibleKernel.comp,Transpose.transpose,
    Holant.Kernel.transpose,Holant.Kernel.mul_apply,column_pairing,one_mul]
  ring

theorem column_pairing_common (T A B C : Holant.Kernel AlgebraicComplex) (s t : AlgebraicComplex)
    (hb : ∀ v, B v false = s * A v false) (hc : ∀ v, C v false = t * A v false) :
    column_pairing T B C = s * t * column_pairing T A A := by
  simp only [column_pairing,hb,hc]
  ring

section Pure
variable {K : Type} [Field K] {r : ℕ} {b : ℕ → ℕ}
variable {H : (i : Fin r) → Holant.Signature K (b i.val)}

theorem decorate_image (phi : K →+* AlgebraicComplex) (N : Macro H 3) (binary : Macro H 2)
    (A B C T : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote = W.image A.matrix B.matrix C.matrix)
    (binaryForm : RingHomRealization.mapSignature phi binary.network.denote = kernelSignature T.matrix) :
    RingHomRealization.mapSignature phi (D.decorate N binary).network.denote =
      W.image A.matrix ((Transpose.transpose T).comp B).matrix C.matrix := by
  funext x
  rw [RingHomRealization.mapSignature,D.decorate,Macro.contract_denote]
  simp only [Macro.reindex_denote,Macro.tensor_denote,Holant.Tensor.reindex_apply,Holant.Signature.tensor_apply]
  have first (v : Bool) :
      (fun i : Fin 3 => (Fin.cons v (Fin.cons v x) : Fin 5 → Bool) (D.order (Fin.castAdd 2 i))) = ![x 0,v,x 2] := by
    funext i
    fin_cases i <;> rfl
  have second (v : Bool) :
      (fun i : Fin 2 => (Fin.cons v (Fin.cons v x) : Fin 5 → Bool) (D.order (Fin.natAdd 3 i))) = ![v,x 1] := by
    funext i
    fin_cases i <;> rfl
  simp only [first,second,map_add,map_mul]
  have nf (v : Bool) : phi (N.network.denote ![x 0,v,x 2]) = W.image A.matrix B.matrix C.matrix ![x 0,v,x 2] :=
    congrFun form _
  have df (v : Bool) : phi (binary.network.denote ![v,x 1]) = kernelSignature T.matrix ![v,x 1] :=
    congrFun binaryForm _
  simp [nf,df,W.image,kernelSignature,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Holant.Tractable.InvertibleKernel.comp,Transpose.transpose,Holant.Kernel.transpose,Holant.Kernel.mul_apply]
  ring

theorem binary_good_output (phi : K →+* AlgebraicComplex) (N : Macro H 3) (binary : Macro H 2)
    (A B C T : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote = W.image A.matrix B.matrix C.matrix)
    (binaryForm : RingHomRealization.mapSignature phi binary.network.denote = kernelSignature T.matrix)
    (breaksLine : column_pairing T.matrix B.matrix C.matrix ≠ 0) :
    ∃ out : Macro H 3, ∃ Q : Holant.Tractable.InvertibleKernel,
      RingHomRealization.mapSignature phi out.network.denote = Forms.ghz Q.matrix := by
  have good : W.gram (1 : AlgebraicComplex) ((Transpose.transpose T).comp B).matrix C.matrix false false ≠ 0 := by
    rwa [gram_after]
  obtain ⟨Q,hQ⟩ := good_triangle phi (D.decorate N binary) A ((Transpose.transpose T).comp B) C
    (decorate_image phi N binary A B C T form binaryForm) good
  exact ⟨G.triangle (D.decorate N binary),Q,hQ⟩
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

include back in
theorem binary_break_hard
    (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted)
    (negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (N : Macro H 3) (pin0 : Macro H 1) (c : K) (hc : c ≠ 0)
    (pin : pin0.network.denote = fun x => c * QuaternaryUnaryAccess.pin false x)
    (binary : Macro H 2) (A B C T : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature K.subtype N.network.denote = W.image A.matrix B.matrix C.matrix)
    (binaryForm : RingHomRealization.mapSignature K.subtype binary.network.denote = kernelSignature T.matrix)
    (breaksLine : column_pairing T.matrix B.matrix C.matrix ≠ 0) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  obtain ⟨out,Q,hQ⟩ := binary_good_output K.subtype N binary A B C T form binaryForm breaksLine
  exact scalar_symmetric_ghz_hard K F H L back P PG PR PF PN negative out pin0 c hc Q hQ pin

include back in
/-- The whole-family escape producer only needs to break the one common
line; its nonzero proportionality scalars are recovered from the W deck. -/
theorem binary_break_isotropic_hard
    (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted)
    (negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (N : Macro H 3) (pin0 : Macro H 1) (c : K) (hc : c ≠ 0)
    (pin : pin0.network.denote = fun x => c * QuaternaryUnaryAccess.pin false x)
    (binary : Macro H 2) (A B C T : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature K.subtype N.network.denote = W.image A.matrix B.matrix C.matrix)
    (bc : W.gram (1 : AlgebraicComplex) B.matrix C.matrix false false = 0)
    (ab : W.gram 1 A.matrix B.matrix false false = 0)
    (ca : W.gram 1 C.matrix A.matrix false false = 0)
    (binaryForm : RingHomRealization.mapSignature K.subtype binary.network.denote = kernelSignature T.matrix)
    (breaksLine : column_pairing T.matrix A.matrix A.matrix ≠ 0) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  obtain ⟨_,_,_,s,t,hs,ht,hb,hc'⟩ := common_isotropic_line A B C bc ab ca
  have good : column_pairing T.matrix B.matrix C.matrix ≠ 0 := by
    rw [column_pairing_common T.matrix A.matrix B.matrix C.matrix s t hb hc']
    exact mul_ne_zero (mul_ne_zero hs ht) breaksLine
  exact binary_break_hard K F H L back P PG PR PF PN negative N pin0 c hc pin binary A B C T form binaryForm good

end
end Paper2.Paper1Proved.OddUnary.TernaryW

