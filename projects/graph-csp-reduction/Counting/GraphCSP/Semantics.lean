import Counting.GraphCSP.Model
import Counting.Model.Graph
import Mathlib.Algebra.BigOperators.Fin

/-!
# Fixed-language graph-to-CSP semantics

The source graph has explicitly indexed vertices and a list of ordered edge
occurrences. The target language has exactly two labels, independent of the
number of vertices: one fixed unary weight and one fixed binary interaction.
The adapter is compared with S1's `MultiGraph.toOpenInstance` at each assignment,
and the final partition equation uses S1's `partition_toOpenInstance` theorem.
-/

open scoped BigOperators

noncomputable section

open Classical

namespace Counting.GraphCSP

variable {D R : Type}

-- Match the classical variable equality used by S1's graph adapter.
local instance (n : Nat) : DecidableEq (Fin n) := fun _ _ => Classical.propDecidable _

/-- A fixed two-label language. `false` denotes the unary weight and `true`
denotes the binary interaction. Its label type does not depend on an instance. -/
def fixedLanguage (M : D → D → R) (w : D → R) : Model.Language D R Bool where
  arity := fun b => if b then 2 else 1
  value := fun b => match b with
    | false => fun x => w (x 0)
    | true => fun x => M (x 0) (x 1)

@[simp] theorem fixedLanguage_unary_arity (M : D → D → R) (w : D → R) :
    (fixedLanguage M w).arity false = 1 := rfl

@[simp] theorem fixedLanguage_binary_arity (M : D → D → R) (w : D → R) :
    (fixedLanguage M w).arity true = 2 := rfl

/-- The language has two labels even when its tables happen to coincide on
some inputs, or when the input graph is empty. -/
theorem fixedLanguage_label_card : Fintype.card Bool = 2 := rfl

namespace Constraint

/-- Translate an ordered unary/binary constraint to S1's occurrence structure. -/
def toOccurrence {n : Nat} (M : D → D → R) (w : D → R) :
    Constraint n → Model.Occurrence (fixedLanguage M w) (Empty ⊕ Fin n)
  | .unary v => ⟨false, fun _ => .inr v⟩
  | .binary u v => ⟨true, fun (i : Fin 2) => .inr (if i = 0 then u else v)⟩

@[simp] theorem eval_unary {n : Nat} (M : D → D → R) (w : D → R)
    (v : Fin n) (a : Empty → D) (b : Fin n → D) :
    (toOccurrence M w (.unary v)).eval (Sum.elim a b) = w (b v) := rfl

@[simp] theorem eval_binary {n : Nat} (M : D → D → R) (w : D → R)
    (u v : Fin n) (a : Empty → D) (b : Fin n → D) :
    (toOccurrence M w (.binary u v)).eval (Sum.elim a b) = M (b u) (b v) := by
  simp [toOccurrence, Model.Occurrence.eval, fixedLanguage, Function.comp_def]

@[simp] theorem binary_scope_zero {n : Nat} (M : D → D → R) (w : D → R)
    (u v : Fin n) : (toOccurrence M w (.binary u v)).scope (0 : Fin 2) = .inr u := by
  simp [toOccurrence]

@[simp] theorem binary_scope_one {n : Nat} (M : D → D → R) (w : D → R)
    (u v : Fin n) : (toOccurrence M w (.binary u v)).scope (1 : Fin 2) = .inr v := by
  simp [toOccurrence]

/-- A loop repeats a variable in the two ordered ports. -/
theorem loop_scope {n : Nat} (M : D → D → R) (w : D → R) (v : Fin n) :
    (toOccurrence M w (.binary v v)).scope (0 : Fin 2) =
      (toOccurrence M w (.binary v v)).scope (1 : Fin 2) := by simp

end Constraint

namespace CSP

/-- Interpret every listed target constraint, retaining all declared variables. -/
def toOpenInstance (I : CSP) (M : D → D → R) (w : D → R) :
    Model.OpenInstance (fixedLanguage M w) Empty (Fin I.n) where
  occurrences := I.constraints.map (Constraint.toOccurrence M w)

/-- The target natural-valued evaluation is the corresponding finite partition
sum; this definition also makes sense over any commutative semiring. -/
def partition [Fintype D] [CommSemiring R] (I : CSP)
    (M : D → D → R) (w : D → R) : R :=
  (I.toOpenInstance M w).partition Empty.elim

@[simp] theorem toOpenInstance_occurrences_length (I : CSP)
    (M : D → D → R) (w : D → R) :
    (I.toOpenInstance M w).occurrences.length = I.constraints.length := by
  simp [toOpenInstance]

end CSP

namespace Graph

/-- Edge identifiers are positions in the edge list, so equal endpoint pairs
remain distinct edge occurrences. -/
def toMultiGraph (G : Graph) : Model.MultiGraph (Fin G.n) (Fin G.edges.length) where
  src e := (G.edges.get e).1
  dst e := (G.edges.get e).2

/-- The source graph evaluation with a fixed interaction and fixed unary weight. -/
def partition [Fintype D] [CommSemiring R] (G : Graph)
    (M : D → D → R) (w : D → R) : R :=
  G.toMultiGraph.partition M (fun _ => w)

/-- The executable target enumeration has the same product as the abstract
S1 graph enumeration. No symmetry, nonzero, or nonempty-domain assumption is used. -/
theorem eval_toCSP [CommMonoid R] (G : Graph) (M : D → D → R) (w : D → R)
    (a : Empty → D) (b : Fin G.n → D) :
    (G.toCSP.toOpenInstance M w).eval a b =
      G.toMultiGraph.assignmentWeight M (fun _ => w) b := by
  simp only [CSP.toOpenInstance, toCSP, Model.OpenInstance.eval,
    List.map_append, List.map_map, List.prod_append, Function.comp_def,
    Constraint.eval_unary, Constraint.eval_binary]
  rw [Model.MultiGraph.assignmentWeight, Fin.prod_univ_def]
  congr 1
  simpa [toMultiGraph, List.get_eq_getElem] using
    (Fin.prod_univ_fun_getElem G.edges (fun e => M (b e.1) (b e.2))).symm

/-- A direct comparison with the per-vertex-labelled S1 adapter. -/
theorem eval_toCSP_eq_toOpenInstance [CommMonoid R]
    (G : Graph) (M : D → D → R) (w : D → R)
    (a : Empty → D) (b : Fin G.n → D) :
    (G.toCSP.toOpenInstance M w).eval a b =
      (G.toMultiGraph.toOpenInstance M (fun _ => w)).eval a b := by
  rw [Model.MultiGraph.eval_toOpenInstance, eval_toCSP]

/-- The executable fixed-language target and the S1 graph adapter have equal
partition values, despite using different label types and enumerations. -/
theorem partition_toCSP_eq_toOpenInstance [Fintype D] [CommSemiring R]
    (G : Graph) (M : D → D → R) (w : D → R) (a : Empty → D) :
    (G.toCSP.toOpenInstance M w).partition a =
      (G.toMultiGraph.toOpenInstance M (fun _ => w)).partition a := by
  unfold Model.OpenInstance.partition
  exact Finset.sum_congr rfl (fun b _ => eval_toCSP_eq_toOpenInstance G M w a b)

/-- The value equation used by the machine-valued counting reduction. Its final
step is precisely S1's graph-to-occurrence partition theorem. -/
@[simp] theorem partition_toCSP [Fintype D] [CommSemiring R]
    (G : Graph) (M : D → D → R) (w : D → R) :
    G.toCSP.partition M w = G.partition M w := by
  unfold CSP.partition Graph.partition
  rw [partition_toCSP_eq_toOpenInstance,
    Model.MultiGraph.partition_toOpenInstance]

/-- With no edges, every declared vertex still carries a unary weight. -/
theorem partition_edgeless [Fintype D] [CommSemiring R]
    (n : Nat) (M : D → D → R) (w : D → R) :
    (Graph.mk n []).partition M w = (∑ d, w d) ^ n := by
  simp only [partition, Model.MultiGraph.partition, Model.MultiGraph.assignmentWeight]
  convert (Fintype.sum_pow w n).symm using 1
  apply Finset.sum_congr
  · ext a
    simp
  · intro a _
    simp

/-- The null graph has one assignment, including when the spin domain is empty. -/
@[simp] theorem partition_null [Fintype D] [CommSemiring R]
    (M : D → D → R) (w : D → R) :
    (Graph.mk 0 []).partition M w = 1 := by
  rw [partition_edgeless, pow_zero]

/-- An isolated vertex contributes its complete unary sum. -/
@[simp] theorem partition_isolated [Fintype D] [CommSemiring R]
    (M : D → D → R) (w : D → R) :
    (Graph.mk 1 []).partition M w = ∑ d, w d := by
  rw [partition_edgeless, pow_one]

/-- The target retains the same edgeless value, including all isolated vertices. -/
theorem partition_toCSP_edgeless [Fintype D] [CommSemiring R]
    (n : Nat) (M : D → D → R) (w : D → R) :
    (Graph.mk n []).toCSP.partition M w = (∑ d, w d) ^ n := by
  rw [partition_toCSP, partition_edgeless]

end Graph

/-- Compress the redundant vertex labels in S1's graph language when every
vertex has the same fixed unary weight. Ordered scopes are copied exactly. -/
def compressGraphOccurrence {V X : Type} (M : D → D → R) (w : D → R) :
    Model.Occurrence (Model.MultiGraph.graphLanguage M (fun _ : V => w)) X →
      Model.Occurrence (fixedLanguage M w) X
  | ⟨.inl _, s⟩ => ⟨false, s⟩
  | ⟨.inr _, s⟩ => ⟨true, s⟩

/-- Compression is valid because the unary table is fixed, not because distinct
vertex labels were silently assumed to belong to a graph-independent language. -/
@[simp] theorem eval_compressGraphOccurrence {V X : Type}
    (M : D → D → R) (w : D → R)
    (c : Model.Occurrence (Model.MultiGraph.graphLanguage M (fun _ : V => w)) X)
    (a : X → D) :
    (compressGraphOccurrence M w c).eval a = c.eval a := by
  rcases c with ⟨v | u, s⟩ <;> rfl

/-- Compress all labels of an open graph-language instance without changing
its variable types, occurrence multiplicities, or ordered scopes. -/
def compressGraphInstance {V B H : Type} (M : D → D → R) (w : D → R)
    (I : Model.OpenInstance (Model.MultiGraph.graphLanguage M (fun _ : V => w)) B H) :
    Model.OpenInstance (fixedLanguage M w) B H where
  occurrences := I.occurrences.map (compressGraphOccurrence M w)

@[simp] theorem eval_compressGraphInstance {V B H : Type} [CommMonoid R]
    (M : D → D → R) (w : D → R)
    (I : Model.OpenInstance (Model.MultiGraph.graphLanguage M (fun _ : V => w)) B H)
    (a : B → D) (b : H → D) :
    (compressGraphInstance M w I).eval a b = I.eval a b := by
  simp [compressGraphInstance, Model.OpenInstance.eval, List.map_map,
    Function.comp_def]

@[simp] theorem partition_compressGraphInstance {V B H : Type}
    [Fintype D] [Fintype H] [DecidableEq H] [CommSemiring R]
    (M : D → D → R) (w : D → R)
    (I : Model.OpenInstance (Model.MultiGraph.graphLanguage M (fun _ : V => w)) B H)
    (a : B → D) :
    (compressGraphInstance M w I).partition a = I.partition a := by
  simp [Model.OpenInstance.partition]

end Counting.GraphCSP
