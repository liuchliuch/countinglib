import Counting.Bridge.OpenNetwork
import Counting.Model.FiniteSums

/-! The corrected tensor has one additional explicit boundary-kernel occurrence
per ordered coordinate, and the former boundary word is summed as hidden data. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Counting.Bridge.OpenNetwork

open Counting.Model
variable {R : Type} [CommSemiring R] {n : Nat}

/-- Original vertex/wire labels plus exactly the supplied boundary kernels. -/
def tensorLanguage (N : _root_.Holant.OpenNetwork R n) :
    Language Bool R ((Fin N.shape.vertices ⊕ Fin N.shape.edges) ⊕ Fin n) where
  arity := Sum.elim (language N).arity (fun _ => 2)
  value := fun label => match label with
    | .inl l => (language N).value l
    | .inr j => fun a => N.boundaryKernel j (a (0 : Fin 2)) (a (1 : Fin 2))

/-- Move all original variables behind the newly supplied external boundary. -/
def internalOccurrence (N : _root_.Holant.OpenNetwork R n)
    (c : Occurrence (language N) (Fin n ⊕ Hidden N)) :
    Occurrence (tensorLanguage N) (Fin n ⊕ (Fin n ⊕ Hidden N)) where
  symbol := .inl c.symbol
  scope := fun i => .inr (c.scope i)

/-- Kernel orientation is external coordinate first, original raw coordinate second. -/
def boundaryOccurrence (N : _root_.Holant.OpenNetwork R n) (j : Fin n) :
    Occurrence (tensorLanguage N) (Fin n ⊕ (Fin n ⊕ Hidden N)) where
  symbol := .inr j
  scope := fun i => if i.val = 0 then .inl j else .inr (.inl j)

/-- Corrected S1 instance: old occurrences followed by the explicit boundary kernels. -/
def toTensorInstance (N : _root_.Holant.OpenNetwork R n) :
    OpenInstance (tensorLanguage N) (Fin n) (Fin n ⊕ Hidden N) where
  occurrences := (toOpenInstance N).occurrences.map (internalOccurrence N) ++
    List.ofFn (boundaryOccurrence N)

@[simp] theorem tensor_occurrences_length (N : _root_.Holant.OpenNetwork R n) :
    (toTensorInstance N).occurrences.length = N.shape.vertices + N.shape.edges + n := by
  simp [toTensorInstance]

@[simp] theorem eval_internalOccurrence (N : _root_.Holant.OpenNetwork R n)
    (c : Occurrence (language N) (Fin n ⊕ Hidden N)) (x y : Fin n → Bool)
    (h : Hidden N → Bool) :
    (internalOccurrence N c).eval (Sum.elim x (Sum.elim y h)) =
      c.eval (Sum.elim y h) := rfl

@[simp] theorem eval_boundaryOccurrence (N : _root_.Holant.OpenNetwork R n)
    (j : Fin n) (x y : Fin n → Bool) (h : Hidden N → Bool) :
    (boundaryOccurrence N j).eval (Sum.elim x (Sum.elim y h)) =
      N.boundaryKernel j (x j) (y j) := by
  simp [Occurrence.eval, boundaryOccurrence, tensorLanguage]

theorem eval_toTensorInstance (N : _root_.Holant.OpenNetwork R n)
    (x y : Fin n → Bool) (h : Hidden N → Bool) :
    (toTensorInstance N).eval x (Sum.elim y h) =
      (∏ j, N.boundaryKernel j (x j) (y j)) * (toOpenInstance N).eval y h := by
  simp [OpenInstance.eval, toTensorInstance, List.map_ofFn, List.prod_ofFn, List.map_map,
    Function.comp_def, mul_comm]

/-- The explicit extra occurrences implement the specified coordinate action. -/
theorem partition_toTensorInstance_action (N : _root_.Holant.OpenNetwork R n)
    (x : Fin n → Bool) :
    (toTensorInstance N).partition x =
      _root_.Holant.Signature.coordinateAction N.boundaryKernel
        (fun y => (toOpenInstance N).partition y) x := by
  unfold OpenInstance.partition _root_.Holant.Signature.coordinateAction
  rw [Counting.Model.FiniteSums.sum_sum_assignments]
  simp only [eval_toTensorInstance, Finset.mul_sum]

/-- Corrected and raw tables remain distinct contracts; both quantify every word. -/
theorem partition_toTensorInstance (N : _root_.Holant.OpenNetwork R n)
    (x : Fin n → Bool) : (toTensorInstance N).partition x = N.tensor x := by
  rw [partition_toTensorInstance_action]
  simp only [partition_toOpenInstance, _root_.Holant.OpenNetwork.tensor]

/-- With ordinary boundary coordinates, the explicit correction has identity action. -/
theorem partition_tensor_eq_raw_of_ordinary (N : _root_.Holant.OpenNetwork R n)
    (h : ∀ j, ∃ p, N.shape.boundary j = .inl p) (x : Fin n → Bool) :
    (toTensorInstance N).partition x = (toOpenInstance N).partition x := by
  rw [partition_toTensorInstance, partition_toOpenInstance,
    _root_.Holant.OpenNetwork.tensor_eq_raw_of_ordinary N h]

/-- In particular, the closed scalar agrees with the raw S1 scalar. -/
theorem partition_tensor_eq_raw_closed (N : _root_.Holant.OpenNetwork R 0)
    (x : Fin 0 → Bool) :
    (toTensorInstance N).partition x = (toOpenInstance N).partition x := by
  rw [partition_toTensorInstance, partition_toOpenInstance,
    _root_.Holant.OpenNetwork.tensor_eq_raw_closed]

end Counting.Bridge.OpenNetwork
