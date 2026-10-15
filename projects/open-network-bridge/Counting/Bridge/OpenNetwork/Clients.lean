import Counting.Bridge.OpenNetwork.Composition
import Holant.VertexGadget

/-!
# Concrete full-open-network clients

The unary native disequality wire has a genuine paired free endpoint; its raw
and corrected tables differ. Two actual disjoint compositions and a canonical
boundary permutation exercise both commuting squares at exact natural values.
-/
noncomputable section
namespace Counting.Bridge.OpenNetwork.Clients


def stubShape : Holant.OpenNetworkShape 1 where
  vertices := 1
  arity := fun _ => 1
  free := 1
  edges := 1
  boundary := ⟨fun _ => .inr 0, fun _ _ _ => Subsingleton.elim _ _⟩
  ends := ⟨fun q => if q.2 then .inr 0 else .inl ⟨0, 0⟩, by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    apply Prod.ext (Subsingleton.elim _ _)
    cases x <;> cases y <;> simp_all⟩
  ordinary_boundary_iff_unpaired := by decide
  freeBoundary := fun _ => 0
  free_boundary := by decide
  freeEdge := fun _ => (0, true)
  free_paired := by decide

def stub : Holant.OpenNetwork ℕ 1 where
  shape := stubShape
  vertex := fun _ x => if x ⟨0, by simp [stubShape]⟩ then 3 else 2
  edge := fun _ => .disequality

theorem stub_paired : stub.shape.ends (⟨0, by decide⟩, true) = stub.shape.boundary 0 := rfl

theorem stub_raw_false : stub.raw (fun _ => false) = 3 := by
  decide

theorem stub_raw_true : stub.raw (fun _ => true) = 2 := by
  decide

theorem stub_tensor_false : stub.tensor (fun _ => false) = 2 := by
  decide

theorem stub_tensor_true : stub.tensor (fun _ => true) = 3 := by
  decide



theorem raw_stub (x : Fin 1 → Bool) : stub.raw x = if x 0 then 2 else 3 := by
  have hx : x = fun _ => x 0 := funext (fun j => congrArg x (Subsingleton.elim j 0))
  rw [hx]
  cases x 0
  · exact stub_raw_false
  · exact stub_raw_true

theorem tensor_stub (x : Fin 1 → Bool) : stub.tensor x = if x 0 then 3 else 2 := by
  have hx : x = fun _ => x 0 := funext (fun j => congrArg x (Subsingleton.elim j 0))
  rw [hx]
  cases x 0
  · exact stub_tensor_false
  · exact stub_tensor_true

theorem stub_boundaryKernel_nonidentity :
    stub.boundaryKernel 0 false true = 1 ∧ stub.boundaryKernel 0 false false = 0 := by
  decide

theorem stub_raw_ne_tensor : stub.raw (fun _ => false) ≠ stub.tensor (fun _ => false) := by
  rw [stub_raw_false, stub_tensor_false]
  decide

/-- An ordinary unary vertex supplies a different factor for the reorder test. -/
def ordinary : Holant.OpenNetwork ℕ 1 :=
  Holant.OpenNetwork.singleVertex (fun x => if x 0 then 7 else 5)

/-- First actual native disjoint composition. -/
def pair : Holant.OpenNetwork ℕ 2 := disjoint stub ordinary

/-- The canonical source operation actually swaps the two boundary positions. -/
def reordered : Holant.OpenNetwork ℕ 2 :=
  Holant.Dihedral.CompatibleClosure.reorderOpen pair (Equiv.swap 0 1)

/-- Second actual native composition, after the nonidentity boundary permutation. -/
def twice : Holant.OpenNetwork ℕ 3 := disjoint reordered stub

def pairWord : Fin 2 → Bool := ![false, true]
def twiceWord : Fin 3 → Bool := ![false, true, true]

theorem ordinary_edges (e : Fin ordinary.shape.edges) : ordinary.edge e = .disequality :=
  Fin.elim0 e

theorem pair_edges : ∀ e, pair.edge e = .disequality :=
  edges_disjoint stub ordinary .disequality (fun _ => rfl) ordinary_edges

theorem reordered_edges : ∀ e, reordered.edge e = .disequality := pair_edges

theorem pair_raw (x : Fin 2 → Bool) :
    pair.raw x = (if x 0 then 2 else 3) * (if x 1 then 7 else 5) := by
  rw [pair, raw_disjoint, Holant.Signature.tensor_apply,
    raw_stub, ordinary, Holant.OpenNetwork.raw_vertex]
  rfl

theorem pair_tensor (x : Fin 2 → Bool) :
    pair.tensor x = (if x 0 then 3 else 2) * (if x 1 then 7 else 5) := by
  rw [pair, tensor_disjoint stub ordinary .disequality (fun _ => rfl) ordinary_edges,
    Holant.Signature.tensor_apply, tensor_stub, ordinary, Holant.OpenNetwork.tensor_vertex]
  rfl

theorem reordered_raw (x : Fin 2 → Bool) :
    reordered.raw x = (if x 1 then 2 else 3) * (if x 0 then 7 else 5) := by
  rw [reordered, Holant.Dihedral.CompatibleClosure.reorderOpen_raw]
  change pair.raw (fun i => x ((Equiv.swap 0 1).symm i)) = _
  rw [pair_raw]
  simp

theorem reordered_tensor (x : Fin 2 → Bool) :
    reordered.tensor x = (if x 1 then 3 else 2) * (if x 0 then 7 else 5) := by
  rw [reordered, Holant.Dihedral.CompatibleClosure.reorderOpen_tensor]
  change pair.tensor (fun i => x ((Equiv.swap 0 1).symm i)) = _
  rw [pair_tensor]
  simp

theorem twice_raw (x : Fin 3 → Bool) :
    twice.raw x =
      ((if x 1 then 2 else 3) * (if x 0 then 7 else 5)) * (if x 2 then 2 else 3) := by
  rw [twice, raw_disjoint, Holant.Signature.tensor_apply, reordered_raw, raw_stub]
  rfl

theorem twice_tensor (x : Fin 3 → Bool) :
    twice.tensor x =
      ((if x 1 then 3 else 2) * (if x 0 then 7 else 5)) * (if x 2 then 3 else 2) := by
  rw [twice, tensor_disjoint reordered stub .disequality reordered_edges (fun _ => rfl),
    Holant.Signature.tensor_apply, reordered_tensor, tensor_stub]
  rfl

attribute [local instance] Classical.propDecidable

/-- The raw bridge has the value 3 at the paired free stub. -/
theorem partition_stub_raw : (toOpenInstance stub).partition (fun _ => false) = 3 := by
  rw [partition_toOpenInstance, stub_raw_false]

/-- The explicit boundary correction changes that same entry to 2. -/
theorem partition_stub_tensor : (toTensorInstance stub).partition (fun _ => false) = 2 := by
  rw [partition_toTensorInstance, stub_tensor_false]

/-- Adapt-after-compose and the literal first S1 composition both evaluate to 21. -/
theorem first_composition_raw :
    (toOpenInstance pair).partition pairWord = 21 ∧
      (disjointInstance stub ordinary).partition pairWord = 21 := by
  have h : (toOpenInstance pair).partition pairWord = 21 := by
    rw [partition_toOpenInstance, pair_raw]
    rfl
  exact ⟨h, (partition_disjoint_commutes stub ordinary pairWord).symm.trans h⟩

/-- The corresponding corrected first composition evaluates to 14. -/
theorem first_composition_tensor :
    (toTensorInstance pair).partition pairWord = 14 ∧
      (disjointTensorInstance stub ordinary).partition pairWord = 14 := by
  have h : (toTensorInstance pair).partition pairWord = 14 := by
    rw [partition_toTensorInstance, pair_tensor]
    rfl
  exact ⟨h, (partition_disjointTensor_commutes stub ordinary .disequality
    (fun _ => rfl) ordinary_edges pairWord).symm.trans h⟩

/-- Reordering changes 21 to 10 and commutes with the actual S1 variable rename. -/
theorem boundary_reorder_raw :
    (toOpenInstance reordered).partition pairWord = 10 ∧
      ((toOpenInstance pair).renameBoundary (Equiv.swap 0 1).symm).partition pairWord = 10 := by
  have h : (toOpenInstance reordered).partition pairWord = 10 := by
    rw [partition_toOpenInstance, reordered_raw]
    rfl
  exact ⟨h, (partition_reorder_commutes pair (Equiv.swap 0 1) pairWord).symm.trans h⟩

/-- The reordered corrected table is 15, with the kernels transported in order. -/
theorem boundary_reorder_tensor :
    (toTensorInstance reordered).partition pairWord = 15 ∧
      ((toTensorInstance pair).renameBoundary (Equiv.swap 0 1).symm).partition pairWord = 15 := by
  have h : (toTensorInstance reordered).partition pairWord = 15 := by
    rw [partition_toTensorInstance, reordered_tensor]
    rfl
  exact ⟨h, (partition_tensor_reorder_commutes pair (Equiv.swap 0 1) pairWord).symm.trans h⟩

/-- Both actual routes through the second native/S1 composition evaluate to 20. -/
theorem second_composition_raw :
    (toOpenInstance twice).partition twiceWord = 20 ∧
      (disjointInstance reordered stub).partition twiceWord = 20 := by
  have h : (toOpenInstance twice).partition twiceWord = 20 := by
    rw [partition_toOpenInstance, twice_raw]
    rfl
  exact ⟨h, (partition_disjoint_commutes reordered stub twiceWord).symm.trans h⟩

/-- At the identical word the corrected second composition evaluates to 45. -/
theorem second_composition_tensor :
    (toTensorInstance twice).partition twiceWord = 45 ∧
      (disjointTensorInstance reordered stub).partition twiceWord = 45 := by
  have h : (toTensorInstance twice).partition twiceWord = 45 := by
    rw [partition_toTensorInstance, twice_tensor]
    rfl
  exact ⟨h, (partition_disjointTensor_commutes reordered stub .disequality
    reordered_edges (fun _ => rfl) twiceWord).symm.trans h⟩

end Counting.Bridge.OpenNetwork.Clients
