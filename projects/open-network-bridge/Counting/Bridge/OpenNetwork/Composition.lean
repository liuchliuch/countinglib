import Counting.Bridge.OpenNetwork.Canonical
import Counting.Gadget.Composition
import Counting.Bridge.OpenNetwork.Corrected
/-!
# Composition of canonical open networks through S1

The source operation is the canonical finite disjoint network followed by its
canonical finite enumeration. The target operation concatenates actual lifted
occurrence lists with `Counting.Gadget.disjointUnion`; the coproduct language
retains each source label, table, port order, and occurrence multiplicity.
-/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Counting.Bridge.OpenNetwork
open Counting.Model
open Holant.OpenNetworkComposition
variable {D R ι κ B H : Type}

/-- Keep both supplied palettes without adding any signatures. -/
def sumLanguage (L : Language D R ι) (M : Language D R κ) : Language D R (ι ⊕ κ) where
  arity := Sum.elim L.arity M.arity
  value := fun s => match s with
    | .inl i => L.value i
    | .inr j => M.value j

/-- Relabel every actual occurrence by the left palette injection. -/
def liftLeft (L : Language D R ι) (M : Language D R κ)
    (I : OpenInstance L B H) : OpenInstance (sumLanguage L M) B H :=
  ⟨I.occurrences.map (fun c => ⟨.inl c.symbol, c.scope⟩)⟩

/-- Relabel every actual occurrence by the right palette injection. -/
def liftRight (L : Language D R ι) (M : Language D R κ)
    (I : OpenInstance M B H) : OpenInstance (sumLanguage L M) B H :=
  ⟨I.occurrences.map (fun c => ⟨.inr c.symbol, c.scope⟩)⟩

@[simp] theorem eval_liftLeft [CommMonoid R] (L : Language D R ι) (M : Language D R κ)
    (I : OpenInstance L B H) (a : B → D) (b : H → D) :
    (liftLeft L M I).eval a b = I.eval a b := by
  simp [OpenInstance.eval, liftLeft, Occurrence.eval, sumLanguage, Function.comp_def]

@[simp] theorem eval_liftRight [CommMonoid R] (L : Language D R ι) (M : Language D R κ)
    (I : OpenInstance M B H) (a : B → D) (b : H → D) :
    (liftRight L M I).eval a b = I.eval a b := by
  simp [OpenInstance.eval, liftRight, Occurrence.eval, sumLanguage, Function.comp_def]

@[simp] theorem partition_liftLeft [CommSemiring R] [Fintype D] [Fintype H] [DecidableEq H]
    (L : Language D R ι) (M : Language D R κ) (I : OpenInstance L B H) (a : B → D) :
    (liftLeft L M I).partition a = I.partition a := by
  simp [OpenInstance.partition]

@[simp] theorem partition_liftRight [CommSemiring R] [Fintype D] [Fintype H] [DecidableEq H]
    (L : Language D R ι) (M : Language D R κ) (I : OpenInstance M B H) (a : B → D) :
    (liftRight L M I).partition a = I.partition a := by
  simp [OpenInstance.partition]

variable {m n : ℕ}
/-- The upstream disjoint incidence construction, enumerated as an OpenNetwork. -/
def disjoint (N : Holant.OpenNetwork R m) (M : Holant.OpenNetwork R n) :
    Holant.OpenNetwork R (m+n) :=
  (DisjointTensor.network (FiniteNetwork.ofOpen N) (FiniteNetwork.ofOpen M)).toOpen

set_option backward.isDefEq.respectTransparency false in
theorem raw_ofOpen [CommSemiring R] (N : Holant.OpenNetwork R n) :
    (FiniteNetwork.ofOpen N).raw = N.raw := by
  classical
  funext x
  unfold FiniteNetwork.raw Holant.OpenNetwork.raw
  apply Finset.sum_congr
  · exact congrArg (fun i : Fintype (Holant.OpenPorts N.shape.vertices N.shape.arity N.shape.free → Bool) => @Finset.univ _ i) (Subsingleton.elim _ _)
  · intro z _
    rfl

theorem raw_disjoint [CommSemiring R] (N : Holant.OpenNetwork R m) (M : Holant.OpenNetwork R n) :
    (disjoint N M).raw = Holant.Signature.tensor N.raw M.raw := by
  rw [disjoint, FiniteNetwork.raw_toOpen, DisjointTensor.network_raw, raw_ofOpen, raw_ofOpen]

theorem tensor_disjoint [CommSemiring R] (N : Holant.OpenNetwork R m) (M : Holant.OpenNetwork R n)
    (W : Holant.EdgeKind) (hN : ∀ e, N.edge e = W) (hM : ∀ e, M.edge e = W) :
    (disjoint N M).tensor = Holant.Signature.tensor N.tensor M.tensor := by
  rw [disjoint, FiniteNetwork.tensor_toOpen,
    DisjointTensor.network_tensor _ _ W hN hM,
    FiniteNetwork.ofOpen_tensor, FiniteNetwork.ofOpen_tensor]

/-- Canonical disjoint union preserves a supplied native edge-kind restriction. -/
theorem edges_disjoint (N : Holant.OpenNetwork R m) (M : Holant.OpenNetwork R n)
    (W : Holant.EdgeKind) (hN : ∀ e, N.edge e = W) (hM : ∀ e, M.edge e = W) :
    ∀ e, (disjoint N M).edge e = W := by
  intro e
  exact DisjointTensor.network_edges (FiniteNetwork.ofOpen N) (FiniteNetwork.ofOpen M)
    W hN hM ((Fintype.equivFin _).symm e)

/-- Compose the two actual raw adapters using S1 disjoint union, then retain the
canonical left-before-right boundary numbering. -/
def disjointInstance [CommSemiring R]
    (N : Holant.OpenNetwork R m) (M : Holant.OpenNetwork R n) :
    OpenInstance (sumLanguage (language N) (language M))
      (Fin (m+n)) (Hidden N ⊕ Hidden M) :=
  (Gadget.disjointUnion
    (liftLeft (language N) (language M) (toOpenInstance N))
    (liftRight (language N) (language M) (toOpenInstance M))).renameBoundary finSumFinEquiv

/-- Literal S1 composition retains every occurrence of both raw adapters. -/
theorem disjointInstance_occurrences_length [CommSemiring R]
    (N : Holant.OpenNetwork R m) (M : Holant.OpenNetwork R n) :
    (disjointInstance N M).occurrences.length =
      (N.shape.vertices + N.shape.edges) + (M.shape.vertices + M.shape.edges) := by
  simp [disjointInstance, Gadget.disjointUnion, Gadget.glue, OpenInstance.renameBoundary,
    OpenInstance.renameHidden, liftLeft, liftRight]

/-- S1's actual composition has the expected native raw product at every word. -/
theorem partition_disjointInstance [CommSemiring R]
    (N : Holant.OpenNetwork R m) (M : Holant.OpenNetwork R n) (x : Fin (m+n) → Bool) :
    (disjointInstance N M).partition x =
      N.raw (fun j => x (Fin.castAdd n j)) * M.raw (fun j => x (Fin.natAdd m j)) := by
  simp only [disjointInstance, OpenInstance.partition_renameBoundary,
    Gadget.partition_disjointUnion, partition_liftLeft, partition_liftRight,
    partition_toOpenInstance]
  rfl

/-- Adapting the canonical native composition agrees with composing the two S1
adapters. This compares actual constructions for every boundary assignment. -/
theorem partition_disjoint_commutes [CommSemiring R]
    (N : Holant.OpenNetwork R m) (M : Holant.OpenNetwork R n) (x : Fin (m+n) → Bool) :
    (toOpenInstance (disjoint N M)).partition x = (disjointInstance N M).partition x := by
  rw [partition_toOpenInstance, raw_disjoint, partition_disjointInstance]
  rfl

/-- Corrected adapters compose by the same S1 operation, with both original
boundary words retained as independent hidden blocks. -/
def disjointTensorInstance [CommSemiring R]
    (N : Holant.OpenNetwork R m) (M : Holant.OpenNetwork R n) :
    OpenInstance (sumLanguage (tensorLanguage N) (tensorLanguage M))
      (Fin (m+n)) ((Fin m ⊕ Hidden N) ⊕ (Fin n ⊕ Hidden M)) :=
  (Gadget.disjointUnion
    (liftLeft (tensorLanguage N) (tensorLanguage M) (toTensorInstance N))
    (liftRight (tensorLanguage N) (tensorLanguage M) (toTensorInstance M))).renameBoundary
      finSumFinEquiv

/-- The corrected S1 composition keeps the two specified kernel actions. -/
theorem partition_disjointTensorInstance [CommSemiring R]
    (N : Holant.OpenNetwork R m) (M : Holant.OpenNetwork R n) (x : Fin (m+n) → Bool) :
    (disjointTensorInstance N M).partition x =
      N.tensor (fun j => x (Fin.castAdd n j)) * M.tensor (fun j => x (Fin.natAdd m j)) := by
  simp only [disjointTensorInstance, OpenInstance.partition_renameBoundary,
    Gadget.partition_disjointUnion, partition_liftLeft, partition_liftRight,
    partition_toTensorInstance]
  rfl

/-- The canonical corrected composition law, with its native common-edge-kind
hypotheses stated explicitly, commutes with the corrected S1 bridge. -/
theorem partition_disjointTensor_commutes [CommSemiring R]
    (N : Holant.OpenNetwork R m) (M : Holant.OpenNetwork R n)
    (W : Holant.EdgeKind) (hN : ∀ e, N.edge e = W) (hM : ∀ e, M.edge e = W)
    (x : Fin (m+n) → Bool) :
    (toTensorInstance (disjoint N M)).partition x =
      (disjointTensorInstance N M).partition x := by
  rw [partition_toTensorInstance, tensor_disjoint N M W hN hM,
    partition_disjointTensorInstance]
  rfl

/-- Boundary permutations commute with the raw adapter and S1 renaming. -/
theorem partition_reorder_commutes [CommSemiring R] (N : Holant.OpenNetwork R n)
    (p : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    (toOpenInstance (Holant.Dihedral.CompatibleClosure.reorderOpen N p)).partition x =
      ((toOpenInstance N).renameBoundary p.symm).partition x := by
  rw [partition_toOpenInstance, Holant.Dihedral.CompatibleClosure.reorderOpen_raw,
    OpenInstance.partition_renameBoundary, partition_toOpenInstance]
  rfl

/-- Boundary permutations also transport every explicit correction kernel. -/
theorem partition_tensor_reorder_commutes [CommSemiring R] (N : Holant.OpenNetwork R n)
    (p : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    (toTensorInstance (Holant.Dihedral.CompatibleClosure.reorderOpen N p)).partition x =
      ((toTensorInstance N).renameBoundary p.symm).partition x := by
  rw [partition_toTensorInstance, Holant.Dihedral.CompatibleClosure.reorderOpen_tensor,
    OpenInstance.partition_renameBoundary, partition_toTensorInstance]
  rfl

end Counting.Bridge.OpenNetwork
