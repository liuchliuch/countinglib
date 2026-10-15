import Paper2.ChargeProducts
import Paper2.EndpointSelfLoop
import Paper2.Realization
import Paper2.NetworkContraction
import Paper2.NetworkGluing.Finite

/-! Concrete resource-labelled native-X networks for arbitrary finite external
port types. Reindexing and self-loop closure are proved by actual graph
constructors, rather than assumed as closure properties of an abstract set. -/
namespace Paper2

namespace Network
variable {K : Type*} {m n : ℕ}

def Uses (N : Network K n) (F : SignatureFamily K) : Prop :=
  ∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature K) ∈ F

def NativeX [Semiring K] (N : Network K n) : Prop :=
  ∀ e, N.edge e = Signature.disequality

/-- Change only the ordered boundary labels; no vertex or edge is altered. -/
def reindexBoundary (e : Fin n ≃ Fin m) (N : Network K n) : Network K m where
  shape := {
    vertices := N.shape.vertices
    arity := N.shape.arity
    edges := N.shape.edges
    ports := N.shape.ports.trans (Equiv.sumCongr e (Equiv.refl _)) }
  vertex := N.vertex
  edge := N.edge

theorem denote_reindexBoundary [CommSemiring K] (e : Fin n ≃ Fin m) (N : Network K n) :
    (reindexBoundary e N).denote = Tensor.reindex e N.denote := by
  funext x
  have ha : ∀ z v i, (reindexBoundary e N).shape.assignment x z v i =
      N.shape.assignment (fun j => x (e j)) z v i := by
    intro z v i
    dsimp only [NetworkShape.assignment, reindexBoundary, Equiv.trans_apply]
    cases N.shape.ports ⟨v, i⟩ <;> rfl
  simp only [Network.denote, Tensor.reindex]
  congr 1
  funext z
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext i
  exact ha z v i

lemma Uses.reindexBoundary {N : Network K n} {F : SignatureFamily K}
    (h : N.Uses F) (e : Fin n ≃ Fin m) : (N.reindexBoundary e).Uses F := h

lemma NativeX.reindexBoundary [Semiring K] {N : Network K n}
    (h : N.NativeX) (e : Fin n ≃ Fin m) : (N.reindexBoundary e).NativeX := h

lemma Uses.contract {N : Network K (n + 2)} {F : SignatureFamily K}
    (h : N.Uses F) (E : Bool → Bool → K) : (N.contract E).Uses F := h

lemma NativeX.contract [Semiring K] {N : Network K (n + 2)} (h : N.NativeX) :
    (N.contract Signature.disequality).NativeX := by
  intro e
  refine Fin.cases ?_ (fun i => ?_) e
  · rfl
  · exact h i
end Network

/-- A real finite network with every local signature in F and every internal
wire literally X. The boundary equivalence is explicit and retains all ports. -/
def NetworkRealizable {K ι : Type} [CommSemiring K]
    (F : SignatureFamily K) (f : Tensor K ι) : Prop :=
  ∃ n, ∃ N : Network K n, ∃ e : Fin n ≃ ι,
    N.Uses F ∧ N.NativeX ∧ Tensor.reindex e N.denote = f

namespace NetworkRealizable
variable {K ι κ : Type} [CommSemiring K] {F : SignatureFamily K}

lemma reindex {f : Tensor K ι} (h : NetworkRealizable F f) (e : ι ≃ κ) :
    NetworkRealizable F (Tensor.reindex e f) := by
  obtain ⟨n, N, eN, hU, hX, hf⟩ := h
  exact ⟨n, N, eN.trans e, hU, hX, by rw [← Tensor.reindex_trans, hf]⟩

/-- Reorder two last distinguished ports into the first two ordered positions. -/
noncomputable def frontPair (ι : Type) [Fintype ι] : Fin (Fintype.card ι + 2) ≃ (ι ⊕ Bool) where
  toFun i := Fin.cases (.inr false)
    (fun j => Fin.cases (.inr true) (fun k => .inl ((Fintype.equivFin ι).symm k)) j) i
  invFun
    | .inl i => ((Fintype.equivFin ι) i).succ.succ
    | .inr b => if b then 1 else 0
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · simp
  right_inv x := by
    cases x with
    | inl i => simp
    | inr b => cases b <;> rfl

lemma contract_frontPair [Fintype ι] (f : Tensor K (ι ⊕ Bool)) :
    Tensor.reindex (Fintype.equivFin ι).symm
      (Signature.contract Signature.disequality (Tensor.reindex (frontPair ι).symm f)) =
        Tensor.contractX f := by
  funext x
  rw [Tensor.reindex_apply, Signature.contract_disequality]
  simp only [Tensor.reindex_apply, Tensor.contractX, Fintype.sum_bool]
  rw [add_comm]
  congr 1 <;> congr 1 <;> funext i <;> cases i with
  | inl i => simp [frontPair]
  | inr b => cases b <;> rfl

lemma selfLoop {f : Tensor K (ι ⊕ Bool)} (h : NetworkRealizable F f) :
    NetworkRealizable F (Tensor.contractX f) := by
  classical
  obtain ⟨n, N, e, hU, hX, hf⟩ := h
  letI : Fintype (ι ⊕ Bool) := Fintype.ofEquiv (Fin n) e
  letI : Fintype ι := Fintype.ofInjective (@Sum.inl ι Bool) Sum.inl_injective
  let M := N.reindexBoundary (e.trans (frontPair ι).symm)
  have hM : M.denote = Tensor.reindex (frontPair ι).symm f := by
    rw [Network.denote_reindexBoundary, ← Tensor.reindex_trans, hf]
  refine ⟨Fintype.card ι, M.contract Signature.disequality,
    (Fintype.equivFin ι).symm, (hU.reindexBoundary _).contract _,
    (hX.reindexBoundary _).contract, ?_⟩
  rw [Network.denote_contract, hM]
  exact contract_frontPair f

/-- Disjoint actual vertices with all ports exposed and no internal edges.
The empty family is the empty nullary network, with value one. -/
noncomputable def edgeless {V : Type} [Fintype V] (r : V → ℕ)
    (f : (v : V) → Signature K (r v)) :
    FiniteNetwork K V Empty (Fintype.card (Σ v, Fin (r v))) where
  arity := r
  ports := {
    toFun := fun p => .inl ((Fintype.equivFin (Σ v, Fin (r v))) p)
    invFun := Sum.elim (Fintype.equivFin (Σ v, Fin (r v))).symm (fun p => Empty.elim p.1)
    left_inv := by intro p; simp
    right_inv := by
      intro p
      cases p with
      | inl i => simp
      | inr p => exact Empty.elim p.1 }
  vertex := f
  edge := fun e => Empty.elim e

lemma edgeless_denote {V : Type} [Fintype V] (r : V → ℕ)
    (f : (v : V) → Signature K (r v)) :
    Tensor.reindex (Fintype.equivFin (Σ v, Fin (r v))).symm
      (edgeless r f).toNetwork.denote = Tensor.piTensor f := by
  rw [FiniteNetwork.denote_toNetwork]
  funext x
  simp [Tensor.reindex, FiniteNetwork.denote, edgeless, Tensor.piTensor]
  apply Finset.prod_congr rfl
  intro v _
  apply congrArg (f v)
  funext i
  change x ((Fintype.equivFin (Σ v, Fin (r v))).symm
    ((Fintype.equivFin (Σ v, Fin (r v))) ⟨v, i⟩)) = x ⟨v, i⟩
  rw [Equiv.symm_apply_apply]

/-- A literal finite tensor product of members of F has an actual edgeless
network over F. This is not a freely supplied tensor-closure oracle. -/
lemma piTensor {V : Type} [Fintype V] (r : V → ℕ)
    (f : (v : V) → Signature K (r v))
    (hf : ∀ v, (⟨r v, f v⟩ : AnySignature K) ∈ F) :
    NetworkRealizable F (Tensor.piTensor f) := by
  classical
  refine ⟨_, (edgeless r f).toNetwork,
    (Fintype.equivFin (Σ v, Fin (r v))).symm, ?_, ?_, edgeless_denote r f⟩
  · intro v
    exact hf ((Fintype.equivFin V).symm v)
  · intro e
    have he : e.val < 0 := by simpa [FiniteNetwork.toNetwork, edgeless] using e.isLt
    omega

lemma copies {V : Type} [Fintype V] (n r : V → ℕ)
    (f : (v : V) → Signature K (r v))
    (hf : ∀ v, (⟨r v, f v⟩ : AnySignature K) ∈ F) :
    NetworkRealizable F (ChargeProducts.table n r f) :=
  piTensor (fun v : ChargeProducts.Copies n => r v.1) (fun v => f v.1)
    (fun v => hf v.1)

/-- Every finite self-loop derivation compiles to a genuine network, preserving
all source resource labels and every native-X wire. -/
theorem reachable {f : Tensor K ι} {g : Tensor K κ}
    (h : EndpointSelfLoop.Reachable K f g) (hf : NetworkRealizable F f) :
    NetworkRealizable F g := by
  induction h with
  | refl f => exact hf
  | reindex e f => exact hf.reindex e
  | selfLoop f => exact hf.selfLoop
  | trans h₁ h₂ ih₁ ih₂ => exact ih₂ (ih₁ hf)

/-- A usual ordered signature has an actual network of exactly that boundary
arity, rather than merely an isomorphic unspecified finite port type. -/
theorem ordered {n : ℕ} {f : Signature K n} (h : NetworkRealizable F f) :
    ∃ N : Network K n, N.Uses F ∧ N.NativeX ∧ N.denote = f := by
  obtain ⟨m, N, e, hU, hX, hf⟩ := h
  exact ⟨N.reindexBoundary e, hU.reindexBoundary e, hX.reindexBoundary e,
    (Network.denote_reindexBoundary e N).trans hf⟩
end NetworkRealizable
end Paper2
