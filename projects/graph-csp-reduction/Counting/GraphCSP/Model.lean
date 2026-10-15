import Counting.Model.Graph
import Mathlib.Data.List.FinRange

/-!
# Explicit graphs and fixed-arity constraint instances

Vertex numbers are part of each finite presentation. Edge and constraint lists
retain order and multiplicity; repeated scope entries represent loops.
-/

namespace Counting.GraphCSP

/-- A finite directed incidence presentation, allowing loops and parallel edges. -/
structure Graph where
  n : Nat
  edges : List (Fin n × Fin n)
  deriving DecidableEq

/-- The two resources of the fixed language, with ordered scopes. -/
inductive Constraint (n : Nat) where
  | unary (v : Fin n)
  | binary (u v : Fin n)
  deriving DecidableEq

/-- An arbitrary occurrence list over the fixed unary/binary language. -/
structure CSP where
  n : Nat
  constraints : List (Constraint n)
  deriving DecidableEq

/-- Each vertex contributes a unary occurrence and each edge a binary one. -/
def Graph.toCSP (G : Graph) : CSP where
  n := G.n
  constraints := (List.finRange G.n).map Constraint.unary ++
    G.edges.map (fun e => Constraint.binary e.1 e.2)

@[simp] theorem Graph.toCSP_n (G : Graph) : G.toCSP.n = G.n := rfl

@[simp] theorem Graph.toCSP_constraints_length (G : Graph) :
    G.toCSP.constraints.length = G.n + G.edges.length := by
  simp [Graph.toCSP]

end Counting.GraphCSP
