import Counting.Bridge.OpenNetwork.Assignments
import Holant.OpenNetwork

/-!
# The canonical full OpenNetwork raw table as an S1 occurrence instance

The source is `Holant.OpenNetwork`, including paired free stubs. Only ports
outside the actual boundary image become hidden variables. Every vertex and wire
contributes one occurrence; no equality resource or default color is added.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Counting.Bridge.OpenNetwork

open Counting.Model
variable {R : Type} {n : Nat}

abbrev Ports (N : _root_.Holant.OpenNetwork R n) :=
  _root_.Holant.OpenPorts N.shape.vertices N.shape.arity N.shape.free

abbrev Hidden (N : _root_.Holant.OpenNetwork R n) := BoundaryComplement.Hidden N.shape.boundary

/-- Split the original ports, retaining the original boundary order. -/
def portEquiv (N : _root_.Holant.OpenNetwork R n) : Fin n ⊕ Hidden N ≃ Ports N :=
  BoundaryComplement.ports N.shape.boundary

/-- The complete assignment extending the prescribed boundary and hidden word. -/
def assignment (N : _root_.Holant.OpenNetwork R n) (x : Fin n → Bool)
    (h : Hidden N → Bool) : Ports N → Bool :=
  BoundaryComplement.extend N.shape.boundary x h

/-- Explicit assignment bijection for the actual canonical OpenNetwork boundary. -/
def assignmentEquiv (N : _root_.Holant.OpenNetwork R n) (x : Fin n → Bool) :
    (Hidden N → Bool) ≃ {z : Ports N → Bool // ∀ j, z (N.shape.boundary j) = x j} :=
  BoundaryComplement.compatibleAssignments N.shape.boundary x

/-- The instance-specific finite palette exposes all actual edge kernels. -/
def language [CommSemiring R] (N : _root_.Holant.OpenNetwork R n) :
    Language Bool R (Fin N.shape.vertices ⊕ Fin N.shape.edges) where
  arity := Sum.elim N.shape.arity (fun _ => 2)
  value := fun label => match label with
    | .inl v => N.vertex v
    | .inr e => fun a => (N.edge e).value (a (0 : Fin 2)) (a (1 : Fin 2))

def vertexOccurrence [CommSemiring R] (N : _root_.Holant.OpenNetwork R n)
    (v : Fin N.shape.vertices) : Occurrence (language N) (Fin n ⊕ Hidden N) where
  symbol := .inl v
  scope := fun i => (portEquiv N).symm (.inl ⟨v, i⟩)

def edgeOccurrence [CommSemiring R] (N : _root_.Holant.OpenNetwork R n)
    (e : Fin N.shape.edges) : Occurrence (language N) (Fin n ⊕ Hidden N) where
  symbol := .inr e
  scope := fun i => (portEquiv N).symm (N.shape.ends (e, if i.val = 0 then false else true))

/-- The actual vertex and edge occurrence lists, including nullary vertices. -/
def toOpenInstance [CommSemiring R] (N : _root_.Holant.OpenNetwork R n) :
    OpenInstance (language N) (Fin n) (Hidden N) where
  occurrences := List.ofFn (vertexOccurrence N) ++ List.ofFn (edgeOccurrence N)

@[simp] theorem occurrences_length [CommSemiring R] (N : _root_.Holant.OpenNetwork R n) :
    (toOpenInstance N).occurrences.length = N.shape.vertices + N.shape.edges := by
  simp [toOpenInstance]

@[simp] theorem eval_vertexOccurrence [CommSemiring R] (N : _root_.Holant.OpenNetwork R n)
    (v : Fin N.shape.vertices) (x : Fin n → Bool) (h : Hidden N → Bool) :
    (vertexOccurrence N v).eval (Sum.elim x h) =
      N.vertex v (fun i => assignment N x h (.inl ⟨v, i⟩)) := rfl

@[simp] theorem eval_edgeOccurrence [CommSemiring R] (N : _root_.Holant.OpenNetwork R n)
    (e : Fin N.shape.edges) (x : Fin n → Bool) (h : Hidden N → Bool) :
    (edgeOccurrence N e).eval (Sum.elim x h) =
      (N.edge e).value (assignment N x h (N.shape.ends (e, false)))
        (assignment N x h (N.shape.ends (e, true))) := by
  simp [Occurrence.eval, edgeOccurrence, language, assignment, portEquiv,
    BoundaryComplement.extend]

/-- Each original half-edge assignment has exactly its original product weight. -/
theorem eval_toOpenInstance [CommSemiring R] (N : _root_.Holant.OpenNetwork R n)
    (x : Fin n → Bool) (h : Hidden N → Bool) :
    (toOpenInstance N).eval x h = N.weight (assignment N x h) := by
  change (toOpenInstance N).eval x h =
    (∏ v : Fin N.shape.vertices, N.vertex v (fun i => assignment N x h (.inl ⟨v, i⟩))) *
      ∏ e : Fin N.shape.edges, (N.edge e).value
        (assignment N x h (N.shape.ends (e, false)))
        (assignment N x h (N.shape.ends (e, true)))
  simp [OpenInstance.eval, toOpenInstance, List.map_ofFn, List.prod_ofFn]

/-- The pinned S1 table is the canonical raw table for every boundary word. -/
theorem partition_toOpenInstance [CommSemiring R] (N : _root_.Holant.OpenNetwork R n)
    (x : Fin n → Bool) : (toOpenInstance N).partition x = N.raw x := by
  simp only [OpenInstance.partition, eval_toOpenInstance]
  unfold assignment _root_.Holant.OpenNetwork.raw
  convert BoundaryComplement.sum_extend N.shape.boundary x N.weight using 2 <;>
    congr 1
  exact Subsingleton.elim _ _

end Counting.Bridge.OpenNetwork
