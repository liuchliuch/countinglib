import Paper2.Paper1ProvedOddUnarySourcedEquality
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZOnePin
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZPrepared
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZWeighted
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCommonBasis

/-! Actual ordinary symmetric-GHZ sources close at the unchanged ordinary
oracle. The retained Gram row is used when the construction changes basis. -/
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

namespace TernaryGHZ
namespace W
export GlobalCloseCompletionSymmetricGHZWeighted (extension graph graph_value)
end W
namespace A
export GlobalCloseCompletionIndependentPinsAdjoin
  (Output arity signatures old old_literal newLabel normalized_literal source)
end A
namespace C
export GlobalCloseCompletionSymmetricGHZCapGraph (symmetric cap)
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz)
export GlobalCloseCompletionSymmetricGHZCapSelection (Semisimple)
end C
namespace Prepared
export GlobalCloseCompletionSymmetricGHZPrepared
  (field presentation table source included ternary ternary_value gram_member)
end Prepared
namespace Sem
export GlobalCloseCompletionSymmetricGHZSemantics (output frame)
end Sem

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
theorem weighted_hard
    (negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (N : Macro H 3) (a d : K) (ha : a ≠ 0) (hd : d ≠ 0)
    (form : N.network.denote = C.symmetric a 0 0 d) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  let D := W.extension H F N a d ha hd form
  have hi : GlobalCloseCompletionUnaryDescentSource.ambient K H ⊆
      GlobalCloseCompletionUnaryDescentSource.ambient K D.table := by
    rintro f ⟨i,rfl⟩
    exact ⟨D.old i,congrArg (RingHomRealization.mapAny K.subtype) (D.old_literal i)⟩
  have hn : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K D.table) :=
    fun ht => negative (ht.mono_family hi)
  exact sourced_equality_hard K F D.table L (Programme.compose D.source back) P PG PR PF PN hn
    (W.graph H F N a d ha hd form) D.scalar D.nonzero (W.graph_value H F N a d ha hd form)

include back P PG PR PF PN in
/-- An actual weighted equality graph and a retained Gram row restore the
whole original basis before the canonical Eq4 hardness theorem is applied. -/
theorem normalized_hard
    (original : Holant.SignatureFamily AlgebraicComplex) (finite : original.Finite)
    (negative : ¬ Holant.Tractable.Tract original) (R : Holant.Tractable.InvertibleKernel)
    (included : Holant.Tractable.familyAction R.symm original ⊆
      GlobalCloseCompletionUnaryDescentSource.ambient K H)
    (gram : (⟨2,kernelSignature (Holant.Kernel.pullback Holant.Signature.equality R.matrix)⟩ :
      Holant.AnySignature AlgebraicComplex) ∈ GlobalCloseCompletionUnaryDescentSource.ambient K H)
    (N : Macro H 3) (a d : K) (ha : a ≠ 0) (hd : d ≠ 0)
    (form : N.network.denote = C.symmetric a 0 0 d) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  let D := W.extension H F N a d ha hd form
  let Q := W.graph H F N a d ha hd form
  let out : A.Output D.table 4 := ⟨Q.network,Q.labels,Q.exact,Q.edges⟩
  let J := A.signatures F D.table out D.scalar
  have hi : GlobalCloseCompletionUnaryDescentSource.ambient K H ⊆
      GlobalCloseCompletionUnaryDescentSource.ambient K D.table := by
    rintro f ⟨i,rfl⟩
    exact ⟨D.old i,congrArg (RingHomRealization.mapAny K.subtype) (D.old_literal i)⟩
  have hj : GlobalCloseCompletionUnaryDescentSource.ambient K D.table ⊆
      GlobalCloseCompletionUnaryDescentSource.ambient K J := by
    rintro f ⟨i,rfl⟩
    exact ⟨A.old D.table i,congrArg (RingHomRealization.mapAny K.subtype)
      (A.old_literal F D.table out D.scalar i)⟩
  have hv : out.network.denote = fun x => D.scalar * Holant.EightVertex.ProductAnchor.equalityFour x :=
    W.graph_value H F N a d ha hd form
  have he := A.normalized_literal F D.table out D.scalar
    Holant.EightVertex.ProductAnchor.equalityFour D.nonzero hv
  have eq4 : (⟨4,Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorCriterion.eq4⟩ :
      Holant.AnySignature AlgebraicComplex) ∈ GlobalCloseCompletionUnaryDescentSource.ambient K J := by
    refine ⟨A.newLabel D.table,?_⟩
    refine (congrArg (RingHomRealization.mapAny K.subtype) he).trans ?_
    apply congrArg (fun f : Holant.Signature AlgebraicComplex 4 => (⟨4,f⟩ : Holant.AnySignature AlgebraicComplex))
    funext x
    simp [RingHomRealization.mapSignature,Holant.EightVertex.ProductAnchor.equalityFour,
      Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorCriterion.eq4]
  have hn : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K J) := by
    intro ht
    exact negative (GlobalCloseCompletionSymmetricGHZCommonBasis.tract original _ finite R
      (fun f hf => hj (hi (included hf))) (hj (hi gram)) eq4 ht)
  let graph : Macro J 4 := Macro.row (A.newLabel D.table) Holant.EightVertex.ProductAnchor.equalityFour he
  have graphValue : graph.network.denote = fun x => (1 : K) * Holant.EightVertex.ProductAnchor.equalityFour x := by
    rw [Macro.row_denote]
    simp
  exact sourced_equality_hard K F J L
    (Programme.compose (A.source F D.table out D.scalar D.nonzero) (Programme.compose D.source back))
    P PG PR PF PN hn graph 1 one_ne_zero graphValue

include back P PG PR PF PN in
theorem prepared_hard
    (negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (N : Macro H 3) (U : Macro H 1) (M : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature K.subtype N.network.denote = C.ghz M.matrix)
    (det : Matrix.det (binaryMatrix (C.cap N U).network.denote) ≠ 0)
    (semisimple : C.Semisimple (binaryMatrix (C.cap N U).network.denote)) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  let C0 := Sem.output H (C.cap N U)
  let D := GlobalCloseCompletionSymmetricGHZRootInverse.produce K F H C0 det semisimple
  obtain ⟨R,normalized,p,q,hp,hq,weighted⟩ := Sem.frame K F H N U M form D det
  let K' := Prepared.field K F H N C0 D R
  let : Algebra ℚ K' := K'.algebra'
  let T := Prepared.table K F H N C0 D R
  let ternary := Prepared.ternary K F H N C0 D R
  have ternaryValue : RingHomRealization.mapSignature K'.subtype ternary.network.denote =
      C.symmetric p 0 0 q :=
    (Prepared.ternary_value K F H N C0 D R).trans ((congrArg R.symm.action form).trans weighted)
  obtain ⟨u,v,hu,hv,shape⟩ := GlobalCloseCompletionSymmetricGHZRows.weighted K'.subtype T ternary p q hp hq ternaryValue
  exact normalized_hard K' (Prepared.presentation K F H N C0 D R) T L
    (Programme.compose (Prepared.source K F H N C0 D R normalized) back) P PG PR PF PN
    (GlobalCloseCompletionUnaryDescentSource.ambient K H) (Set.finite_range _) negative R
    (Prepared.included K F H N C0 D R) (Prepared.gram_member K F H N C0 D R normalized)
    ternary u v hu hv shape

include back P PG PR PF PN in
theorem symmetric_ghz_hard
    (negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (N : Macro H 3) (pin0 : Macro H 1) (M : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature K.subtype N.network.denote = C.ghz M.matrix)
    (pin : pin0.network.denote = QuaternaryUnaryAccess.pin false) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  rcases GlobalCloseCompletionSymmetricGHZOnePin.produce K.subtype N pin0 M form pin with
    ⟨a,d,ha,hd,weighted⟩ | ⟨U,det,semisimple⟩
  · exact weighted_hard K F H L back P PG PR PF PN negative N a d ha hd weighted
  · exact prepared_hard K F H L back P PG PR PF PN negative N U M form det semisimple

end TernaryGHZ
end
end Paper2.Paper1Proved.OddUnary

