import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryFramedSelector
import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesComplete

/-! The paired exit of the actual nonisotropic unary selector needs no Z
resource. This interface uses exactly its ordinary graph and scalar zero pin,
and retains the controlled field-table reduction in the equality receipt. -/
namespace Paper2.Paper1Proved.OddUnary.Paired
noncomputable section
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open OrdinaryNegativeCubicGadgets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {s degree : ℕ} {a : ℕ → ℕ}
variable (H : (i : Fin s) → Holant.Signature K (a i.val))
variable (F : FixedField K degree) (phi : K →+* ℂ)
variable (U : NoXOrdinaryGraphAdjoin.Output H 1)
variable (c : K) (hc : c ≠ 0)
variable (h0 : U.network.denote (fun _ => false) = c)
variable (h1 : U.network.denote (fun _ => true) = 0)
variable (N : NoXOrdinaryGraphAdjoin.Output H 4)
variable (support : GlobalCloseCompletionUnaryQuaternaryForm.Paired N.network.denote)
variable (nonsingular : GlobalCloseCompletionUnaryQuaternaryForm.determinant N.network.denote ≠ 0)

def matrix : Matrix Bool Bool K := fun p q => N.network.denote ![p,p,q,q]

def graph : Macro H 4 :=
  (show Macro H 4 from ⟨N.network,N.labels,N.exact,N.ordinary⟩).reindex (Equiv.swap 1 2)

def pin : Macro H 1 := ⟨U.network,U.labels,U.exact,U.ordinary⟩

include support in
omit [Algebra ℚ K] [CharZero K] in
theorem graph_form : (graph H N).network.denote = GlobalCloseCompletionPairedSeriesCore.row (matrix H N) := by
  rw [graph,Macro.reindex_denote]
  funext x
  have word : (fun i => x ((Equiv.swap (1 : Fin 4) 2) i)) = ![x 0,x 2,x 1,x 3] := by
    funext i
    fin_cases i <;> rfl
  change N.network.denote (fun i => x ((Equiv.swap 1 2) i)) = _
  rw [word]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [GlobalCloseCompletionPairedSeriesCore.row,matrix,h0,h1,h2,h3]
  all_goals apply support; simp

include nonsingular in
omit [Algebra ℚ K] [CharZero K] in
theorem matrix_nonsingular : (matrix H N).det ≠ 0 := by
  rw [Holant.Complexity.BinaryInterpolation.det_entries]
  exact nonsingular

def receipt : GlobalCloseCompletionPairedSeriesReceipt.Receipt H F :=
  GlobalCloseCompletionPairedSeriesComplete.produce H F phi (graph H N) (matrix H N)
    (graph_form H N support) (matrix_nonsingular H N nonsingular)
    (pin H U) c hc h0 h1

section Subfield
variable (L : IntermediateField ℚ Holant.Tractable.AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
local instance : CharZero L := Algebra.charZero_of_charZero ℚ L
variable (J : (i : Fin s) → Holant.Signature L (a i.val)) (E : FixedField L degree)
variable (W : NoXOrdinaryGraphAdjoin.Output J 1)
variable (d : L) (hd : d ≠ 0) (hd0 : W.network.denote (fun _ => false) = d)
variable (hd1 : W.network.denote (fun _ => true) = 0)
variable (Q : NoXOrdinaryGraphAdjoin.Output J 4)
variable (hq : GlobalCloseCompletionUnaryQuaternaryForm.Paired Q.network.denote)
variable (hm : GlobalCloseCompletionUnaryQuaternaryForm.determinant Q.network.denote ≠ 0)

def complexEmbedding : L →+* ℂ := (algebraicClosure ℚ ℂ).subtype.comp L.subtype

abbrev subfieldReceipt := receipt J E (complexEmbedding L) W d hd hd0 hd1 Q hq hm

theorem old_included : GlobalCloseCompletionUnaryDescentSource.ambient L J ⊆
    GlobalCloseCompletionUnaryDescentSource.ambient L
      (subfieldReceipt L J E W d hd hd0 hd1 Q hq hm).table := by
  rintro f ⟨i,rfl⟩
  let D := subfieldReceipt L J E W d hd hd0 hd1 Q hq hm
  exact ⟨D.old i,congrArg (RingHomRealization.mapAny L.subtype) (D.old_literal i)⟩

theorem obstruction
    (negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient L J)) :
    ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient L
      (subfieldReceipt L J E W d hd hd0 hd1 Q hq hm).table) :=
  fun ht => negative (ht.mono_family (old_included L J E W d hd hd0 hd1 Q hq hm))

end Subfield
end
end Paper2.Paper1Proved.OddUnary.Paired

