import Counting.Algorithm.VariableEliminationWidth.Bags

/-!
# Intrinsic paths and running intersection for supplied bag trees

Nodes are the actual indices `Fin bags.length`, so equal bags at distinct list
positions remain distinct nodes. Each attachment adds exactly its declared
leaf-to-parent edge and shifts the old nodes by `Fin.succ`. The global
running-intersection theorem is derived from the local overlap condition.

The module also proves connectivity and strict index increase along directed
parent chains. The latter excludes directed cycles; an undirected simple-path
uniqueness theorem or a `SimpleGraph.IsTree` conversion is not asserted here.
-/

namespace Counting.Algorithm.VariableEliminationWidth

variable {V : Type} [DecidableEq V]

namespace BagTree

/-- A directed edge from one concrete node to its declared parent. -/
inductive ParentEdge : {bags : List (Finset V)} → BagTree bags →
    Fin bags.length → Fin bags.length → Prop where
  | newest {bag : Finset V} {bags : List (Finset V)}
      (rest : BagTree bags) (parent : Fin bags.length)
      (overlap : ∀ other ∈ bags, bag ∩ other ⊆ bags.get parent) :
      ParentEdge (.attach bag rest parent overlap) 0 parent.succ
  | lift {bag : Finset V} {bags : List (Finset V)}
      (rest : BagTree bags) (parent : Fin bags.length)
      (overlap : ∀ other ∈ bags, bag ∩ other ⊆ bags.get parent)
      {i j : Fin bags.length} (edge : ParentEdge rest i j) :
      ParentEdge (.attach bag rest parent overlap) i.succ j.succ

/-- Undirected adjacency uses only an actual declared parent edge. -/
def Adjacent {bags : List (Finset V)} (tree : BagTree bags)
    (i j : Fin bags.length) : Prop := ParentEdge tree i j ∨ ParentEdge tree j i

theorem ParentEdge.index_lt {bags : List (Finset V)} {tree : BagTree bags}
    {i j : Fin bags.length} (edge : ParentEdge tree i j) : i.val < j.val := by
  induction edge with
  | newest rest parent overlap => exact Nat.zero_lt_succ _
  | lift rest parent overlap edge ih => exact Nat.succ_lt_succ ih

theorem adjacent_symm {bags : List (Finset V)} {tree : BagTree bags}
    {i j : Fin bags.length} (edge : Adjacent tree i j) : Adjacent tree j i :=
  edge.symm

theorem adjacent_irrefl {bags : List (Finset V)} (tree : BagTree bags)
    (i : Fin bags.length) : ¬ Adjacent tree i i := by
  intro edge
  rcases edge with edge | edge <;> exact (Nat.lt_irrefl i.val) edge.index_lt

theorem adjacent_lift {bag : Finset V} {bags : List (Finset V)}
    (rest : BagTree bags) (parent : Fin bags.length)
    (overlap : ∀ other ∈ bags, bag ∩ other ⊆ bags.get parent)
    {i j : Fin bags.length} (edge : Adjacent rest i j) :
    Adjacent (.attach bag rest parent overlap) i.succ j.succ := by
  rcases edge with edge | edge
  · exact Or.inl (.lift rest parent overlap edge)
  · exact Or.inr (.lift rest parent overlap edge)

/-- A finite path whose every node satisfies `allowed`, including both endpoints.
Each step uses an actual parent edge in one of its two directions. -/
inductive Path {bags : List (Finset V)} (tree : BagTree bags)
    (allowed : Fin bags.length → Prop) : Fin bags.length → Fin bags.length → Prop where
  | refl {i : Fin bags.length} (hi : allowed i) : Path tree allowed i i
  | step {i j k : Fin bags.length} (hi : allowed i) (edge : Adjacent tree i j)
      (tail : Path tree allowed j k) : Path tree allowed i k

theorem Path.first {bags : List (Finset V)} {tree : BagTree bags}
    {allowed : Fin bags.length → Prop} {i j : Fin bags.length}
    (path : Path tree allowed i j) : allowed i := by
  cases path with
  | refl hi => exact hi
  | step hi edge tail => exact hi

theorem Path.last {bags : List (Finset V)} {tree : BagTree bags}
    {allowed : Fin bags.length → Prop} {i j : Fin bags.length}
    (path : Path tree allowed i j) : allowed j := by
  induction path with
  | refl hi => exact hi
  | step hi edge tail ih => exact ih

theorem Path.trans {bags : List (Finset V)} {tree : BagTree bags}
    {allowed : Fin bags.length → Prop} {i j k : Fin bags.length}
    (first : Path tree allowed i j) (second : Path tree allowed j k) :
    Path tree allowed i k := by
  induction first generalizing k with
  | refl hi => exact second
  | step hi edge tail ih => exact .step hi edge (ih second)

theorem Path.symm {bags : List (Finset V)} {tree : BagTree bags}
    {allowed : Fin bags.length → Prop} {i j : Fin bags.length}
    (path : Path tree allowed i j) : Path tree allowed j i := by
  induction path with
  | refl hi => exact .refl hi
  | step hi edge tail ih =>
      exact ih.trans (.step tail.first (adjacent_symm edge) (.refl hi))

/-- Old paths retain their exact edges after an attachment shifts the old nodes. -/
theorem Path.lift {bag : Finset V} {bags : List (Finset V)}
    (rest : BagTree bags) (parent : Fin bags.length)
    (overlap : ∀ other ∈ bags, bag ∩ other ⊆ bags.get parent)
    (allowed : Fin (bag :: bags).length → Prop)
    {i j : Fin bags.length} (path : Path rest (fun i => allowed i.succ) i j) :
    Path (.attach bag rest parent overlap) allowed i.succ j.succ := by
  induction path with
  | refl hi => exact .refl hi
  | step hi edge tail ih => exact .step hi (adjacent_lift rest parent overlap edge) ih

/-- In particular, old occurrence paths remain occurrence paths after lifting. -/
theorem lift_occurrencePath {bag : Finset V} {bags : List (Finset V)}
    (rest : BagTree bags) (parent : Fin bags.length)
    (overlap : ∀ other ∈ bags, bag ∩ other ⊆ bags.get parent)
    (v : V) {i j : Fin bags.length}
    (path : Path rest (fun i => v ∈ bags.get i) i j) :
    Path (.attach bag rest parent overlap) (fun i => v ∈ (bag :: bags).get i)
      i.succ j.succ :=
  Path.lift rest parent overlap (fun i => v ∈ (bag :: bags).get i) path

/-- Two occurrences of any vertex are connected through bags all containing that
vertex. This is derived from the local input-bag intersection condition alone. -/
theorem runningIntersection {bags : List (Finset V)} (tree : BagTree bags) (v : V) :
    ∀ i j : Fin bags.length, v ∈ bags.get i → v ∈ bags.get j →
      Path tree (fun k => v ∈ bags.get k) i j := by
  induction tree with
  | root bag =>
      intro i j hi hj
      have same : i = j := by
        apply Fin.ext
        have hi' : i.val < 1 := i.isLt
        have hj' : j.val < 1 := j.isLt
        omega
      subst j
      exact .refl hi
  | @attach bag bags rest parent overlap ih =>
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro hi hj
          exact .refl hi
        · intro hi hj
          have hv : v ∈ bag := hi
          have hj' : v ∈ bags.get j := hj
          have hp : v ∈ bags.get parent :=
            leaf_separator bag bags parent overlap v hv (bags.get j) (List.get_mem _ _) hj'
          exact .step hi (Or.inl (.newest rest parent overlap))
            (lift_occurrencePath rest parent overlap v (ih parent j hp hj'))
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro hi hj
          have hv : v ∈ bag := hj
          have hi' : v ∈ bags.get i := hi
          have hp : v ∈ bags.get parent :=
            leaf_separator bag bags parent overlap v hv (bags.get i) (List.get_mem _ _) hi'
          exact (Path.step hj (Or.inl (.newest rest parent overlap))
            (lift_occurrencePath rest parent overlap v (ih parent i hp hi'))).symm
        · intro hi hj
          exact lift_occurrencePath rest parent overlap v (ih i j hi hj)

/-- The distinguished original root, shifted by every later leaf attachment. -/
def rootIndex : {bags : List (Finset V)} → BagTree bags → Fin bags.length
  | _, .root _ => 0
  | _, .attach _ rest _ _ => (rootIndex rest).succ

theorem path_to_root {bags : List (Finset V)} (tree : BagTree bags) :
    ∀ i : Fin bags.length, Path tree (fun _ => True) i tree.rootIndex := by
  induction tree with
  | root bag =>
      intro i
      have same : i = (0 : Fin [bag].length) := by
        apply Fin.ext
        change i.val = 0
        have hi' : i.val < 1 := i.isLt
        omega
      subst i
      exact .refl True.intro
  | @attach bag bags rest parent overlap ih =>
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact .step True.intro (Or.inl (.newest rest parent overlap))
          (Path.lift rest parent overlap (fun _ => True) (ih parent))
      · exact Path.lift rest parent overlap (fun _ => True) (ih i)

/-- The underlying parent-edge graph is connected, even for empty bags. -/
theorem connected {bags : List (Finset V)} (tree : BagTree bags)
    (i j : Fin bags.length) : Path tree (fun _ => True) i j :=
  (path_to_root tree i).trans (path_to_root tree j).symm

/-- A nonempty directed chain of declared parent edges. -/
inductive ParentChain {bags : List (Finset V)} (tree : BagTree bags) :
    Fin bags.length → Fin bags.length → Prop where
  | edge {i j : Fin bags.length} (edge : ParentEdge tree i j) : ParentChain tree i j
  | trans {i j k : Fin bags.length} (first : ParentChain tree i j)
      (second : ParentChain tree j k) : ParentChain tree i k

theorem ParentChain.index_lt {bags : List (Finset V)} {tree : BagTree bags}
    {i j : Fin bags.length} (chain : ParentChain tree i j) : i.val < j.val := by
  induction chain with
  | edge edge => exact edge.index_lt
  | trans first second ihFirst ihSecond => exact Nat.lt_trans ihFirst ihSecond

/-- Directed parent cycles are impossible because each edge strictly increases
the concrete node index. This does not assert an undirected acyclicity theorem. -/
theorem no_parent_cycle {bags : List (Finset V)} (tree : BagTree bags)
    (i : Fin bags.length) : ¬ ParentChain tree i i := by
  intro chain
  exact (Nat.lt_irrefl i.val) chain.index_lt

end BagTree

/-- A supplied decomposition inherits the derived global running-intersection
property without an extra path, bucket-width, or dynamic-scope hypothesis. -/
theorem Decomposition.runningIntersection {width : Nat} (d : Decomposition V width)
    (v : V) (i j : Fin d.bags.length) (hi : v ∈ d.bags.get i) (hj : v ∈ d.bags.get j) :
    BagTree.Path d.tree (fun k => v ∈ d.bags.get k) i j :=
  d.tree.runningIntersection v i j hi hj

end Counting.Algorithm.VariableEliminationWidth
