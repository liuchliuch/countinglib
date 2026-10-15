import Counting.Model.Basic

/-!
# Finite multigraphs as weighted occurrence instances

Vertices and edge occurrences have separate finite types. Repeated endpoints
retain parallel edges; equal endpoints retain loops. Every vertex contributes
one unary occurrence, even if it is isolated. Endpoint order is preserved, so
no symmetry assumption on the interaction table is necessary.
-/

open scoped BigOperators

noncomputable section

open Classical

namespace Counting.Model

/-- An incidence presentation with a separate type of edge occurrences.
No condition forbids loops or repeated pairs of endpoints. -/
structure MultiGraph (V E : Type) where
  src : E → V
  dst : E → V

namespace MultiGraph

variable {V E D R : Type}

/-- The product for one assignment, with a weight table for each vertex. -/
def assignmentWeight [Fintype V] [Fintype E] [CommMonoid R]
    (G : MultiGraph V E) (M : D → D → R) (w : V → D → R) (a : V → D) : R :=
  (∏ v, w v (a v)) * ∏ e, M (a (G.src e)) (a (G.dst e))

/-- Sum over all assignments to all vertices, including isolated vertices. -/
def partition [Fintype V] [Fintype E] [Fintype D] [CommSemiring R]
    (G : MultiGraph V E) (M : D → D → R) (w : V → D → R) : R :=
  ∑ a : V → D, G.assignmentWeight M w a

/-- The exact resources used by the adapter: one unary table per vertex and
one binary interaction table. The finite label type is `V ⊕ Unit`. -/
def graphLanguage (M : D → D → R) (w : V → D → R) : Language D R (V ⊕ Unit) where
  arity := Sum.elim (fun _ => 1) (fun _ => 2)
  value := fun s => match s with
    | .inl v => fun x => w v (x (0 : Fin 1))
    | .inr _ => fun x => M (x (0 : Fin 2)) (x (1 : Fin 2))

/-- A vertex weight, including the weight of an isolated vertex. -/
def vertexOccurrence (M : D → D → R) (w : V → D → R) (v : V) :
    Occurrence (graphLanguage M w) (Empty ⊕ V) where
  symbol := .inl v
  scope := fun _ => .inr v

/-- A binary occurrence with source first and destination second.
A loop uses its vertex at both ports. -/
def edgeOccurrence (G : MultiGraph V E) (M : D → D → R) (w : V → D → R) (e : E) :
    Occurrence (graphLanguage M w) (Empty ⊕ V) where
  symbol := .inr ()
  scope := fun (i : Fin 2) => .inr (if i = 0 then G.src e else G.dst e)

@[simp] theorem edgeOccurrence_scope_zero (G : MultiGraph V E)
    (M : D → D → R) (w : V → D → R) (e : E) :
    (G.edgeOccurrence M w e).scope (0 : Fin 2) = .inr (G.src e) := by
  simp [edgeOccurrence]

@[simp] theorem edgeOccurrence_scope_one (G : MultiGraph V E)
    (M : D → D → R) (w : V → D → R) (e : E) :
    (G.edgeOccurrence M w e).scope (1 : Fin 2) = .inr (G.dst e) := by
  simp [edgeOccurrence]

@[simp] theorem eval_vertexOccurrence (M : D → D → R) (w : V → D → R)
    (v : V) (a : Empty → D) (b : V → D) :
    (vertexOccurrence M w v).eval (Sum.elim a b) = w v (b v) := rfl

@[simp] theorem eval_edgeOccurrence (G : MultiGraph V E)
    (M : D → D → R) (w : V → D → R) (e : E) (a : Empty → D) (b : V → D) :
    (G.edgeOccurrence M w e).eval (Sum.elim a b) = M (b (G.src e)) (b (G.dst e)) := by
  simp [Occurrence.eval, edgeOccurrence, graphLanguage, Function.comp_def]

/-- Enumerate every vertex and every edge occurrence exactly once. The hidden
variable type is the original vertex type, so assignments are unchanged. -/
def toOpenInstance [Fintype V] [Fintype E] (G : MultiGraph V E)
    (M : D → D → R) (w : V → D → R) : OpenInstance (graphLanguage M w) Empty V where
  occurrences := (Finset.univ.toList.map (vertexOccurrence M w)) ++
    (Finset.univ.toList.map (G.edgeOccurrence M w))

/-- The adapter has exactly one occurrence per vertex and per edge occurrence. -/
@[simp] theorem toOpenInstance_occurrences_length [Fintype V] [Fintype E]
    (G : MultiGraph V E) (M : D → D → R) (w : V → D → R) :
    (G.toOpenInstance M w).occurrences.length = Fintype.card V + Fintype.card E := by
  simp [toOpenInstance]

/-- Assignment products agree over a commutative monoid; no summation or
nonempty-domain assumption is needed. -/
@[simp] theorem eval_toOpenInstance [Fintype V] [Fintype E] [CommMonoid R]
    (G : MultiGraph V E) (M : D → D → R) (w : V → D → R)
    (a : Empty → D) (b : V → D) :
    (G.toOpenInstance M w).eval a b = G.assignmentWeight M w b := by
  simp [OpenInstance.eval, toOpenInstance, List.map_map, Function.comp_def,
    Finset.prod_map_toList, assignmentWeight]

/-- The graph-to-CSP adapter preserves the partition value over every finite
domain and every commutative semiring, including the empty domain. -/
@[simp] theorem partition_toOpenInstance [Fintype V] [Fintype E] [Fintype D]
    [CommSemiring R] (G : MultiGraph V E) (M : D → D → R) (w : V → D → R)
    (a : Empty → D) :
    (G.toOpenInstance M w).partition a = G.partition M w := by
  simp [OpenInstance.partition, partition]

end MultiGraph
end Counting.Model
