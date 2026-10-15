import Counting.GraphCSP.Model

/-!
# Structural preservation by the instance transformation

The target type admits arbitrary constraint lists. The transformation preserves
the complete ordered edge list and explicitly emits every vertex, independently
of its degree. No distinctness or loop-freedom condition is imposed.
-/

namespace Counting.GraphCSP

/-- Recover the ordered endpoint pair of a binary occurrence. -/
def Constraint.edge? {n : Nat} : Constraint n → Option (Fin n × Fin n)
  | .unary _ => none
  | .binary u v => some (u, v)

/-- Recover the scope of a unary occurrence. -/
def Constraint.vertex? {n : Nat} : Constraint n → Option (Fin n)
  | .unary v => some v
  | .binary _ _ => none

/-- The ordered binary scopes in a general CSP. -/
def CSP.binaryScopes (I : CSP) : List (Fin I.n × Fin I.n) :=
  I.constraints.filterMap Constraint.edge?

/-- The ordered unary scopes in a general CSP. -/
def CSP.unaryScopes (I : CSP) : List (Fin I.n) :=
  I.constraints.filterMap Constraint.vertex?

@[simp] theorem Graph.toCSP_binaryScopes (G : Graph) :
    G.toCSP.binaryScopes = G.edges := by
  simp [CSP.binaryScopes, Graph.toCSP, List.filterMap_map, Function.comp_def, Constraint.edge?]

@[simp] theorem Graph.toCSP_unaryScopes (G : Graph) :
    G.toCSP.unaryScopes = List.finRange G.n := by
  simp [CSP.unaryScopes, Graph.toCSP, List.filterMap_map, Function.comp_def, Constraint.vertex?]

/-- Every declared vertex, including isolated vertices, appears once as a unary scope. -/
@[simp] theorem Graph.toCSP_unaryCount (G : Graph) :
    G.toCSP.unaryScopes.length = G.n := by simp

/-- The target model permits variables without any constraints at all. -/
def emptyCSP (n : Nat) : CSP := ⟨n, []⟩

@[simp] theorem emptyCSP_unaryScopes (n : Nat) :
    (emptyCSP n).unaryScopes = [] := rfl

/-- The independent CSP model is strictly more general than graph images. -/
theorem emptyCSP_not_graph_image (n : Nat) (hn : 0 < n) :
    ∀ G : Graph, G.toCSP ≠ emptyCSP n := by
  intro G h
  have hsize := congrArg CSP.n h
  have hcount := congrArg (fun I : CSP => I.unaryScopes.length) h
  simp only [Graph.toCSP_unaryCount, emptyCSP_unaryScopes, List.length_nil] at hcount
  simp only [Graph.toCSP_n, emptyCSP] at hsize
  omega

end Counting.GraphCSP
