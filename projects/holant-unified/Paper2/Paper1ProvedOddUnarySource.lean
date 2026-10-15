import Paper2.Paper1ProvedOddUnarySourcedEquality
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryFramedSelector

/-! The ordinary primitive source is lifted into its original coefficient
field and normalized by its actual nonisotropic unary. The chart has a genuine
edge-count correction and a controlled source back to the original Eq oracle.
No Z row, changed-coordinate physical matrix, or odd dichotomy is assumed. -/
namespace Paper2.Paper1Proved.OddUnary.Source
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (L : Language)

abbrev field := GeneralOddHighTerminalAccess.field (signatures L)
local instance : Algebra ℚ (field L) := (field L).algebra'
local instance : CharZero (field L) := Algebra.charZero_of_charZero ℚ (field L)
abbrev presentation := GeneralOddHighTerminalAccess.presentation (signatures L)
abbrev originalTables := OriginalFamily.tables (signatures L) GeneralOddHighTerminalAccess.edges

def table (i : Fin L.count) : Holant.Signature (field L) (L.arity i.val) :=
  fun x => (presentation L).decode ((originalTables L).vertex i x)

theorem table_exact (i : Fin L.count) (x : Fin (L.arity i.val) → Bool) :
    (table L i x : AlgebraicComplex) = L.signature i x :=
  familyCoordinates_spec
    (OriginalFamily.coefficient (signatures L) GeneralOddHighTerminalAccess.edges)
    (OriginalFamily.coefficient_algebraic (signatures L) GeneralOddHighTerminalAccess.edges)
    (.inl ⟨i,x⟩)

theorem edge_exact (i : Fin 1) (u v : Bool) :
    (presentation L).decode ((originalTables L).edge i u v) = Holant.Signature.equality u v := by
  apply Subtype.ext
  have h := familyCoordinates_spec
    (OriginalFamily.coefficient (signatures L) GeneralOddHighTerminalAccess.edges)
    (OriginalFamily.coefficient_algebraic (signatures L) GeneralOddHighTerminalAccess.edges)
    (.inr (i,u,v))
  exact h.trans (by cases u <;> cases v <;> simp [OriginalFamily.coefficient,
    GeneralOddHighTerminalAccess.edges,Holant.Signature.equality])

private theorem tables_ext {d s b : ℕ} {a : ℕ → ℕ}
    (T S : Holant.Complexity.ExactSignatureTables d s b a)
    (hv : T.vertex = S.vertex) (he : T.edge = S.edge) : T = S := by
  cases T
  cases S
  cases hv
  cases he
  rfl

theorem field_tables : QuaternaryOrdinaryCompanion.tables (presentation L) (table L) = originalTables L := by
  apply tables_ext
  · funext i x
    exact (presentation L).decode.symm_apply_apply _
  · funext i u v
    change (presentation L).decode.symm (Holant.Signature.equality u v) = _
    rw [← edge_exact L i u v]
    exact (presentation L).decode.symm_apply_apply _

theorem ambient : GlobalCloseCompletionUnaryDescentSource.ambient (field L) (table L) = L.family := by
  apply congrArg Set.range
  funext i
  apply congrArg (Sigma.mk (L.arity i.val))
  exact funext (table_exact L i)

def back : Holant.Complexity.LengthControlledOracleReduction
    (sourceEncoding L) (presentation L).encoding (sourceEncoding L) (presentation L).encoding
    ((QuaternaryOrdinaryCompanion.tables (presentation L) (table L)).evaluate (presentation L))
    (GeneralOddHighTerminalAccess.targetValue (signatures L)) :=
  controlledOneQueryOfEq (Holant.Complexity.BinaryCompose.identityComputes (sourceEncoding L))
    (Holant.Complexity.BinaryCompose.identityComputes (presentation L).encoding)
    ((originalTables L).outputBound (presentation L))
    ((QuaternaryOrdinaryCompanion.tables (presentation L) (table L)).evaluate (presentation L))
    (fun G => by rw [field_tables]; rfl)

variable (U : GeneralOddHighTerminalAccess.Actual (signatures L) 1)

private theorem cast_any {K : Type} {m n : ℕ} (h : m = n) (f : Holant.Signature K m) :
    (⟨m,f⟩ : Holant.AnySignature K) = ⟨n,fun x => f (fun j => x (Fin.cast h j))⟩ := by
  cases h
  rfl

def first : NoXOrdinaryGraphAdjoin.Output (table L) 1 where
  network := (GeneralOddHighTerminalAccess.labels (signatures L) U).sourceNetwork
    (table L) (fun _ => Holant.Signature.equality)
  labels := GeneralOddHighTerminalAccess.labels (signatures L) U
  exact v := by
    have ha := (GeneralOddHighTerminalAccess.labels (signatures L) U).vertex_arity v
    exact cast_any ha (table L ((GeneralOddHighTerminalAccess.labels (signatures L) U).vertex v))
  ordinary _ := rfl

theorem first_value :
    (fun x => ((first L U).network.denote x : AlgebraicComplex)) = U.graph.denote := by
  have hm : ((first L U).network.map (field L).subtype) =
      (GeneralOddHighTerminalAccess.labels (signatures L) U).sourceNetwork
        (signatures L) GeneralOddHighTerminalAccess.edges := by
    unfold first Holant.Network.map Holant.Complexity.FixedGadgetSubstitution.Labelling.sourceNetwork
    congr 1
    · funext v x
      exact table_exact L _ _
    · funext e u v
      cases u <;> cases v <;> simp [GeneralOddHighTerminalAccess.edges,Holant.Signature.equality]
  funext x
  change (field L).subtype ((first L U).network.denote x) = U.graph.denote x
  rw [← Holant.Network.denote_map (field L).subtype,hm]
  rw [← Holant.Complexity.FixedGadgetSubstitution.Labelling.denote_template]
  exact congrFun (GeneralOddHighTerminalAccess.template_denote (signatures L) U) x

variable (hn : GeneralOddNonisotropicFrame.norm U.graph.denote ≠ 0)
variable (hnot : ¬ Tract L.family)

include hn in
theorem norm_nonzero : GeneralOddNonisotropicFrame.norm (first L U).network.denote ≠ 0 := by
  intro hz
  apply hn
  rw [← first_value L U]
  rw [← GlobalCloseCompletionUnaryDescentSource.norm_map]
  rw [hz]
  rfl

include hnot in
theorem negative : ¬ Holant.Tractable.Tract
    (GlobalCloseCompletionUnaryDescentSource.ambient (field L) (table L)) := by
  rw [ambient]
  exact fun ht => hnot ((tract_iff _).mpr ht)

abbrev chartTable := GlobalCloseCompletionUnaryFramedSelector.table (field L) (table L) (first L U)
abbrev chartPin := GlobalCloseCompletionUnaryFramedSelector.pin (field L) (table L) (first L U)
abbrev chartScalar := GlobalCloseCompletionUnaryFramedSelector.scale (field L) (table L) (first L U)

include hn in
def chartBack : Holant.Complexity.LengthControlledOracleReduction
    (sourceEncoding L) (presentation L).encoding (sourceEncoding L) (presentation L).encoding
    ((QuaternaryOrdinaryCompanion.tables (presentation L) (chartTable L U)).evaluate (presentation L))
    (GeneralOddHighTerminalAccess.targetValue (signatures L)) :=
  Programme.compose
    (GlobalCloseCompletionUnaryChartSource.controlled (presentation L) (table L)
      (first L U).network.denote (norm_nonzero L U hn)) (back L)

def result : GlobalCloseCompletionUnaryUniversalSelector.Produced (chartTable L U) :=
  GlobalCloseCompletionUnaryFramedSelector.result (field L) (table L) (first L U)
    (norm_nonzero L U hn) (negative L hnot)

include hn hnot in
theorem hard_or_residual
    (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted) :
    FixedFieldOutput.SharpPHard .ordinary L ∨
      (∃ N : NoXOrdinaryGraphAdjoin.Output (chartTable L U) 3,
        Holant.LocalDrafts.FinitePGL2.Stabilization.Prime (⟨3,N.network.denote⟩ : Holant.AnySignature (field L))) ∨
      (∃ n, ∃ N : NoXOrdinaryGraphAdjoin.Output (chartTable L U) n,
        0 < n ∧ N.network.denote ≠ 0 ∧ N.network.denote (fun _ => false) = 0) := by
  have hz := norm_nonzero L U hn
  have hc := GlobalCloseCompletionUnaryFramedSelector.scale_nonzero
    (field L) (table L) (first L U) hz
  have h0 := GlobalCloseCompletionUnaryFramedSelector.pin0
    (field L) (table L) (first L U) hz
  have h1 := GlobalCloseCompletionUnaryFramedSelector.pin1
    (field L) (table L) (first L U) hz
  have ht := GlobalCloseCompletionUnaryFramedSelector.obstruction
    (field L) (table L) (first L U) hz (negative L hnot)
  cases result L U hn hnot with
  | ternary N prime => exact Or.inr (Or.inl ⟨N,prime⟩)
  | paired N support nonsingular =>
    exact Or.inl (receipt_hard (field L) (presentation L) (chartTable L U) L
      (chartBack L U hn) P PG PR PF PN ht
      (Paired.subfieldReceipt (field L) (chartTable L U) (presentation L)
        (chartPin L U) (chartScalar L U) hc h0 h1 N support nonsingular))
  | zeroOrigin N positive nonzero zero => exact Or.inr (Or.inr ⟨_,N,positive,nonzero,zero⟩)

end
end Paper2.Paper1Proved.OddUnary.Source


