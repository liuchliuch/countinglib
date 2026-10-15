import Counting.Model.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Ordered half-edge networks with explicit kernels

The incidence convention follows `Holant.NetworkShape`: an ordinary vertex port
is either a boundary port or one of the two distinct ends of an internal edge.
An internal edge contributes its own binary kernel. In particular, no equality
kernel, disequality kernel, pinning resource, or vertex factor is inserted
implicitly. This generalizes the domain of that convention from `Bool` to `D`.

The adapter below expands each vertex and each edge into one occurrence. Its
value theorem is proved from the product and assignment sums on both sides.
It is a bridge between the two definitions in this project, not an import or
verification of a theorem from an upstream Holant release. The additional free
stubs of upstream `Holant.OpenNetwork` are discussed in `notes/HOLANT.md`.
-/

namespace Counting.Model

/-- An ordered ordinary-port incidence shape. The bijection rules out missing,
duplicated, or dangling ordinary ports while allowing loops and parallel edges. -/
structure KernelNetworkShape (B : Type) where
  vertices : Nat
  arity : Fin vertices → Nat
  edges : Nat
  ports : (Σ v : Fin vertices, Fin (arity v)) ≃ (B ⊕ (Fin edges × Bool))

namespace KernelNetworkShape

variable {B D : Type}

/-- Supply one value per boundary port and independently at both ends of every
internal edge. Even an equality edge has two distinct half-edge variables. -/
def assignment (s : KernelNetworkShape B) (x : B → D)
    (z : (Fin s.edges × Bool) → D) (v : Fin s.vertices) : Fin (s.arity v) → D :=
  fun i => Sum.elim x z (s.ports ⟨v, i⟩)

/-- A loop retains two distinct local port occurrences at its common vertex. -/
theorem edge_endpoints_distinct (s : KernelNetworkShape B) (e : Fin s.edges) :
    s.ports.symm (.inr (e, false)) ≠ s.ports.symm (.inr (e, true)) := by
  intro h
  have h' := s.ports.symm.injective h
  cases h'

end KernelNetworkShape

/-- Vertex signatures and binary edge kernels retain separate roles. The edge
kernel can be equality, disequality, or any supplied `D × D` table. -/
structure KernelNetwork (D R B : Type) where
  shape : KernelNetworkShape B
  vertex : (v : Fin shape.vertices) → Signature D R (shape.arity v)
  edge : Fin shape.edges → D → D → R

namespace KernelNetwork

variable {D R B : Type}

/-- Multiply the genuine vertex factors and exactly one factor per edge. -/
def weight [CommMonoid R] (N : KernelNetwork D R B) (x : B → D)
    (z : (Fin N.shape.edges × Bool) → D) : R :=
  (∏ v : Fin N.shape.vertices, N.vertex v (N.shape.assignment x z v)) *
    ∏ e : Fin N.shape.edges, N.edge e (z (e, false)) (z (e, true))

/-- The raw boundary table, with no additional action on boundary coordinates. -/
def raw [CommSemiring R] [Fintype D] (N : KernelNetwork D R B) (x : B → D) : R :=
  ∑ z : (Fin N.shape.edges × Bool) → D, N.weight x z

/-- The finite language used by this instance adapter. Vertex labels and edge
labels are disjoint; every actual kernel is exposed as a binary table. -/
def language (N : KernelNetwork D R B) :
    Language D R (Fin N.shape.vertices ⊕ Fin N.shape.edges) where
  arity := Sum.elim N.shape.arity (fun _ => 2)
  value := fun label => match label with
    | .inl v => N.vertex v
    | .inr e => fun a => N.edge e (a (0 : Fin 2)) (a (1 : Fin 2))

/-- The ordered local ports of one vertex. -/
def vertexOccurrence (N : KernelNetwork D R B) (v : Fin N.shape.vertices) :
    Occurrence N.language (B ⊕ (Fin N.shape.edges × Bool)) where
  symbol := .inl v
  scope := fun i => N.shape.ports ⟨v, i⟩

/-- One edge occurrence, with false/true as its first/second ordered endpoint. -/
def edgeOccurrence (N : KernelNetwork D R B) (e : Fin N.shape.edges) :
    Occurrence N.language (B ⊕ (Fin N.shape.edges × Bool)) where
  symbol := .inr e
  scope := fun i => .inr (e, if i.val = 0 then false else true)

/-- Expand all vertex and edge occurrences, retaining their multiplicities. -/
def toOpenInstance (N : KernelNetwork D R B) :
    OpenInstance N.language B (Fin N.shape.edges × Bool) where
  occurrences := List.ofFn N.vertexOccurrence ++ List.ofFn N.edgeOccurrence

@[simp] theorem occurrences_length (N : KernelNetwork D R B) :
    N.toOpenInstance.occurrences.length = N.shape.vertices + N.shape.edges := by
  simp [toOpenInstance]

@[simp] theorem eval_vertexOccurrence (N : KernelNetwork D R B)
    (v : Fin N.shape.vertices) (x : B → D) (z : (Fin N.shape.edges × Bool) → D) :
    (N.vertexOccurrence v).eval (Sum.elim x z) =
      N.vertex v (N.shape.assignment x z v) := rfl

@[simp] theorem eval_edgeOccurrence (N : KernelNetwork D R B)
    (e : Fin N.shape.edges) (x : B → D) (z : (Fin N.shape.edges × Bool) → D) :
    (N.edgeOccurrence e).eval (Sum.elim x z) =
      N.edge e (z (e, false)) (z (e, true)) := by
  simp [Occurrence.eval, edgeOccurrence, language]

/-- Expansion into constraints preserves every assignment weight. -/
theorem eval_toOpenInstance [CommMonoid R] (N : KernelNetwork D R B)
    (x : B → D) (z : (Fin N.shape.edges × Bool) → D) :
    N.toOpenInstance.eval x z = N.weight x z := by
  simp [OpenInstance.eval, toOpenInstance, List.map_ofFn, List.prod_ofFn, weight]

/-- The complete value bridge, valid also for empty domains, nullary vertices,
zero factors, loops, and parallel edges. -/
theorem partition_toOpenInstance [CommSemiring R] [Fintype D]
    (N : KernelNetwork D R B) (x : B → D) :
    N.toOpenInstance.partition x = N.raw x := by
  simp only [OpenInstance.partition, raw, eval_toOpenInstance]

end KernelNetwork
end Counting.Model
