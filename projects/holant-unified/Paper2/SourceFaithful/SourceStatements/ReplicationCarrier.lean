import Paper2.SourceFaithful.SourceStatements.ReplicationAlgebra
import Paper2.Paper1ProvedNetwork
import Paper2.RelativeEO.Paper1OccurrenceAccepted
import Holant.Proofs.Closure.ClosurePhysicalBridgeHolographicOpenAlgebra

/-! The ordinary-wire copying context and its actual inverse-K image. The
incidence bijection and all three ordered boundary blocks are unchanged. -/
namespace Paper2.SourceFaithful.SourceStatements.Replication
open Paper2.Tractable Paper2.ExactInput Paper2.RelativeEO Paper2.Problem
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure OrdinaryCarrierContext (L : Language) {r s : ℕ}
    (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s) where
  graph : Network AlgebraicComplex (r+(r+s))
  uses : graph.Uses L.family
  nativeI : ∀ e, graph.edge e=Signature.equality
  scalar : AlgebraicComplex
  scalar_ne_zero : scalar≠0
  scalarCode : RootCode
  scalarCode_correct : scalarCode.MinimalRepresents (scalar : ℂ)
  step : ∀ (p : Fin r → Bool) (y : Fin s → Bool),
    (∑ a : Fin r → Bool, g a*graph.denote (Fin.append a (Fin.append p y))) =
      scalar*g p*h y

structure OrdinaryNonzeroTaggedClosure (L : Language) {r : ℕ}
    (g : Signature AlgebraicComplex r) where
  closedInput : TaggedInstance L g (fun k => k=1)
  value_ne_zero : value .ordinary (tagged L g) closedInput.val≠0
  code : RootCode
  code_correct : code.MinimalRepresents (value .ordinary (tagged L g) closedInput.val : ℂ)

def inverseKNetwork {n : ℕ} (G : Network AlgebraicComplex n) : Network AlgebraicComplex n where
  shape := G.shape
  vertex v := sourceKBasis.symm.action (G.vertex v)
  edge e := Kernel.pullback (G.edge e) KMatrix

theorem inverseKNetwork_denote {n : ℕ} (G : Network AlgebraicComplex n) :
    (inverseKNetwork G).denote=sourceKBasis.symm.action G.denote := by
  exact OpenHolographic.denote_transform (Paper1Proved.sourceNetwork G)
    KMatrix KInverse KMatrix_mul_inverse

def OrdinaryCarrierContext.toNative (L : Language) {r s : ℕ}
    (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s)
    (C : OrdinaryCarrierContext L g h) :
    CarrierContext (Synthesis.inverseKLanguage L) (sourceKBasis.symm.action g)
      (sourceKBasis.symm.action h) where
  graph := inverseKNetwork C.graph
  uses := by
    intro v
    rw [Synthesis.inverseKLanguage_family]
    exact ⟨⟨C.graph.shape.arity v,C.graph.vertex v⟩,C.uses v,rfl⟩
  nativeX := by
    intro e
    change Kernel.pullback (C.graph.edge e) KMatrix=Signature.disequality
    rw [C.nativeI e]
    exact sourceKBasis_pullback
  scalar := C.scalar
  scalar_ne_zero := C.scalar_ne_zero
  scalarCode := C.scalarCode
  scalarCode_correct := C.scalarCode_correct
  step := by
    intro p y
    rw [inverseKNetwork_denote]
    exact inverseK_carrier_step g h C.graph.denote C.scalar C.step p y


end
end Paper2.SourceFaithful.SourceStatements.Replication
