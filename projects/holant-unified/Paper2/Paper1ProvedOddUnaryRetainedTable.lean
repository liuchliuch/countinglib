import Paper2.Paper1ProvedOddUnaryTernaryResidual

/-! Literal retention of an ordinary field table preserves every existing
physical graph and its source reduction. This is used when genuine Jordan
interpolation adjoins finitely many original-field unary signatures. -/
namespace Paper2.Paper1Proved.OddUnary.RetainedTable
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
section Generic
variable {K : Type} [Field K] {r s n : ℕ} {a b : ℕ → ℕ}
variable {H : (i : Fin r) → Holant.Signature K (a i.val)}
variable {J : (i : Fin s) → Holant.Signature K (b i.val)}
variable (old : Fin r → Fin s)
variable (literal : ∀ i, (⟨b (old i).val,J (old i)⟩ : Holant.AnySignature K)=⟨a i.val,H i⟩)

/-- The old graph keeps its network, coefficients, edge kernels, and boundary
order; only its retained vertex-label numbers are updated. -/
def lift (N : NoXOrdinaryGraphAdjoin.Output H n) : NoXOrdinaryGraphAdjoin.Output J n where
  network := N.network
  labels := {
    vertex v := old (N.labels.vertex v)
    vertex_arity v := (congrArg Sigma.fst (literal (N.labels.vertex v))).trans
      (N.labels.vertex_arity v)
    edge _ := 0 }
  exact v := (literal (N.labels.vertex v)).trans (N.exact v)
  ordinary := N.ordinary

@[simp] theorem lift_network (N : NoXOrdinaryGraphAdjoin.Output H n) :
    (lift old literal N).network=N.network := rfl

/-- Macro retention also keeps the literal ordinary equality edges. -/
def liftMacro (N : OrdinaryNegativeCubicGadgets.Macro H n) :
    OrdinaryNegativeCubicGadgets.Macro J n where
  network := N.network
  labels := {
    vertex v := old (N.labels.vertex v)
    vertex_arity v := (congrArg Sigma.fst (literal (N.labels.vertex v))).trans
      (N.labels.vertex_arity v)
    edge _ := 0 }
  exact v := (literal (N.labels.vertex v)).trans (N.exact v)
  edges := N.edges

@[simp] theorem macro_network (N : OrdinaryNegativeCubicGadgets.Macro H n) :
    (liftMacro old literal N).network=N.network := rfl

end Generic
section FieldTable
variable {r s : ℕ} {a b : ℕ → ℕ}
variable (Q : IntermediateField ℚ AlgebraicComplex)
variable {H : (i : Fin r) → Holant.Signature Q (a i.val)}
variable {J : (i : Fin s) → Holant.Signature Q (b i.val)}
variable (old : Fin r → Fin s)
variable (literal : ∀ i, (⟨b (old i).val,J (old i)⟩ : Holant.AnySignature Q)=⟨a i.val,H i⟩)

include old literal in
/-- Literal old-row inclusion is enough to preserve the whole-family
obstruction; it is independent of how new unary access was implemented. -/
theorem included : GlobalCloseCompletionUnaryDescentSource.ambient Q H ⊆
    GlobalCloseCompletionUnaryDescentSource.ambient Q J := by
  rintro f ⟨i,rfl⟩
  exact ⟨old i,congrArg (RingHomRealization.mapAny Q.subtype) (literal i)⟩

include old literal in
theorem negative
    (h : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient Q H)) :
    ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient Q J) :=
  fun hJ => h (hJ.mono_family (included Q old literal))

end FieldTable
end
end Paper2.Paper1Proved.OddUnary.RetainedTable

namespace Paper2.Paper1Proved.OddUnary.TernarySource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {L : Paper2.ExactInput.Language} (S : TernarySource L)
variable {s : ℕ} {b : ℕ → ℕ}
variable (J : (i : Fin s) → Holant.Signature S.K (b i.val))
variable (old : Fin S.count → Fin s)
variable (literal : ∀ i, (⟨b (old i).val,J (old i)⟩ : Holant.AnySignature S.K)=⟨S.arity i.val,S.H i⟩)

/-- Adjoining signatures with an honest controlled reduction retains the
same original ordinary target and the same nonisotropic scalar zero pin. -/
def retain
    (old : Fin S.count → Fin s)
    (literal : ∀ i, (⟨b (old i).val,J (old i)⟩ : Holant.AnySignature S.K)=⟨S.arity i.val,S.H i⟩)
    (back : letI : Algebra ℚ S.K := S.K.algebra'; LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding s 1 b) S.F.encoding
      (RawClosedNetwork.validatedEncoding S.count 1 S.arity) S.F.encoding
      ((QuaternaryOrdinaryCompanion.tables S.F J).evaluate S.F)
      ((QuaternaryOrdinaryCompanion.tables S.F S.H).evaluate S.F)) : TernarySource L where
  K := S.K
  degree := S.degree
  F := S.F
  count := s
  arity := b
  H := J
  back := by
    let _ : Algebra ℚ S.K := S.K.algebra'
    exact Programme.compose back S.back
  negative := RetainedTable.negative S.K old literal S.negative
  zeroPin := RetainedTable.lift old literal S.zeroPin
  scalar := S.scalar
  scalarNonzero := S.scalarNonzero
  zeroPinFalse := S.zeroPinFalse
  zeroPinTrue := S.zeroPinTrue
  graph := RetainedTable.lift old literal S.graph
  prime := S.prime

end
end Paper2.Paper1Proved.OddUnary.TernarySource

namespace Paper2.Paper1Proved.OddUnary.IsotropicWSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {L : Paper2.ExactInput.Language} (S : IsotropicWSource L)
variable {s : ℕ} {b : ℕ → ℕ}
variable (J : (i : Fin s) → Holant.Signature S.source.K (b i.val))
variable (old : Fin S.source.count → Fin s)
variable (literal : ∀ i, (⟨b (old i).val,J (old i)⟩ : Holant.AnySignature S.source.K)=
  ⟨S.source.arity i.val,S.source.H i⟩)

/-- The actual isotropic W witness survives a sourced finite unary extension;
no analytical matrix is promoted to a graph label. -/
def retain
    (old : Fin S.source.count → Fin s)
    (literal : ∀ i, (⟨b (old i).val,J (old i)⟩ : Holant.AnySignature S.source.K)=
      ⟨S.source.arity i.val,S.source.H i⟩)
    (back : letI : Algebra ℚ S.source.K := S.source.K.algebra'; LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding s 1 b) S.source.F.encoding
      (RawClosedNetwork.validatedEncoding S.source.count 1 S.source.arity) S.source.F.encoding
      ((QuaternaryOrdinaryCompanion.tables S.source.F J).evaluate S.source.F)
      ((QuaternaryOrdinaryCompanion.tables S.source.F S.source.H).evaluate S.source.F)) :
    IsotropicWSource L where
  source := S.source.retain J old literal back
  residual := by
    obtain ⟨N,A,B,C,form,bc,ab,ca⟩ := S.residual
    exact ⟨RetainedTable.liftMacro old literal N,A,B,C,form,bc,ab,ca⟩

end
end Paper2.Paper1Proved.OddUnary.IsotropicWSource

